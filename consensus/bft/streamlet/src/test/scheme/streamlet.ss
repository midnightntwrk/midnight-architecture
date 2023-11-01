;;; ------------------------------------------------------------------------
;;;                                  Copyright 2023, Input Output Hong Kong
(library (streamlet)
  (export run-tests)
  (import
    (chezscheme)
    (consensus lib common)
    (consensus lib verify)
    (consensus lib leader-election)
    (consensus lib signed-messages)
    (scheme-actors yassam)
    (slib openssl crypto)
    (slib datatype)
    (slib utils))

  (define (bugme label val)
    (bug (format "~a: ~a" (self) label) val))
  
  ;; ------------------------------------------------------------------
  ;; Datatypes

  (define-record-type block
    (nongenerative)
    (fields epoch-number txs parent-hash)
    (protocol
      (lambda (new)
        (lambda (epoch-number txs parent-chain) ;; must specify parent chain, not hash
          (cond
            ;; Genesis block
            [(= epoch-number 0) (new 0 '() (sha256-hash '()))]
            ;; Ordinary block
            [else
              (new epoch-number txs
                (hash-blockchain parent-chain))])))))

  (define (block->bytevector b)
    (let ([tx (make-transcoder (latin-1-codec) (eol-style lf)
                (error-handling-mode replace))])
      (call-with-bytevector-output-port
        (lambda (p)
          (fprintf p "block ~s ~s ~s"
            (block-parent-hash b)
            (block-epoch-number b)
            (block-txs b)))
        tx)))
  
  (define-who (well-formed-block? b)
    ;; Validation of the parent reference happens in context, using
    ;; `well-formed-blockchain?`.
    (verifying who b
      (and (verify (block? b))
           (verify (nonnegative? (block-epoch-number b)))
           (verify (bytevector? (block-parent-hash b)))
           (verifying who [txs (block-txs b)]
             (or (bot? txs)
                 (and
                   (verify (list? txs))
                   (verify (andmap well-formed-transaction? txs))))))))

  ;; Convert a bytevector into a number suitable for Chez hashtable keys.
  (define (hash-bytevector bv)
    (mod (u8-bytevector->integer bv) (expt 2 32))
    )

  (define (make-bytevector-hashtable)
    (make-hashtable
      hash-bytevector
      bytevector=?))

  ;; A block-ext is like an extension table for a SQL table of blocks --
  ;; it holds extra data for each block. Blocks go on the wire, but
  ;; block-ext records are local to each process.  Every block-ext is
  ;; instantiated only once in each process.  We maintain a chain-db for
  ;; looking up a chain by its hash, and a block-db for looking up a
  ;; block to fetch its block-ext. Since chains are a process-local
  ;; construct (not shared on the wire), we represent a chain as a list
  ;; of block-ext rather than block.
  ;;
  ;; We want to manage the computational complexity of determining when
  ;; a chain is fully notarized, to prove to ourselves that looping over
  ;; the whole chain is not required. Our solution makes use of a set of
  ;; forward pointers (beneficiaries) and a set of backward pointers
  ;; (unnotarized-ancestors). A notarized chain is one whose highest
  ;; block is notarized and whose unnotarized-ancestors is an empty set.
  ;;
  ;; Whenever a block-ext a becomes notarized itself, we (1) update all
  ;; the beneficiaries' unnotarized-ancestors, deleting a, and (2) we
  ;; set its beneficiaries list to '().  If this causes a block-ext to
  ;; become the head of the longest notarized chain, we promote it to
  ;; the set of longest-notarized-chains and update
  ;; longest-notarized-length to the length field from the block-ext.
  ;;
  ;; We should also prune defunct block-exts.  A block-ext is defunct
  ;; when there exists a longest-notarized-chain that does not include
  ;; the block-ext's corresponding block. Even notarized blocks can
  ;; become defunct. (Not yet implemented.)
  (define-record-type block-ext
    (nongenerative)
    (fields
      block ;; the block for which this is the ext
      votes ;; signatures
      (mutable notarized?)
      (mutable unnotarized-ancestors) ;; blocks
      (mutable beneficiaries) ;; block-exts
      )
    (protocol
      (lambda (new)
        (lambda (block)
          (new block
            (make-bytevector-hashtable)
            (eq? block genesis-block) ;; auto notarized
            '()
            '())))))
  (define (chain-notarized? chain) ;; assuming a well-formed blockchain
    (and (block-ext-notarized? (car chain))
         (null? (block-ext-unnotarized-ancestors (car chain)))))

  ;; This is an important operation, with side effects, that adds a
  ;; new block-ext to a chain and updates all the mutable pointers
  ;; required to track notarizations.
  (define block-cons
    (case-lambda
      [(epoch-number txs parent-chain)
       (assert (list? parent-chain))
       (block-cons (make-block epoch-number txs parent-chain)
         parent-chain)]
      [(block parent-chain)
       (assert (list? parent-chain))
       (let* ([block-ext (cond
                           [(block? block) (make-block-ext block)]
                           [(block-ext? block) block]
                           [else (errorf 'block-cons "not a block ~s" block)])]
              [parent (car parent-chain)]
              [ls (cons block-ext parent-chain)])
         (block-ext-unnotarized-ancestors-set! block-ext
           (let ([b* (block-ext-unnotarized-ancestors parent)])
             (if (block-ext-notarized? parent)
                 b*
                 (cons parent b*))))
         (for-each
           (lambda (b)
             (block-ext-beneficiaries-set! b
               (cons block-ext
                 (block-ext-beneficiaries b))))
           ls)
         ls)]))
             

  ;; Serialize the block's string representation and hash that.
  (define (hash-block b)
    (assert (block? b))
    (sha256-hash (list (block->bytevector b))))
  
  ;; When we hash a block, we hash just the protocol's notion of the
  ;; block, not the full block-ext record.
  (define (hash-block-ext b)
    (assert (block-ext? b))
    (hash-block (block-ext-block b)))

  ;; Blockchain blocks are a descending linked list (b_h, ..., b_0)
  (define (blockchain? x) (and (list? x) (andmap block-ext? x)))

  ;; Optimistically hash a chain assuming the shape (b_h, ..., b_0) by
  ;; hashing together the block hash of b_h with its parent hash.
  ;; This operation relies on just the first element of the list.  To
  ;; verify a well-formed blockchain, call `well-formed-blockchain?`
  (define (hash-blockchain b*)
    (verifying 'hash-blockchain b*
      (verify (andmap block-ext? b*))
      (verify (block? (block-ext-block (car b*)))))
    (cond
      [(null? b*) (sha256-hash '())]
      [(= 1 (length b*))
       (assert (eq? (car b*) genesis-block-ext))
       (hash-block-ext genesis-block-ext)]
      [else (let ([pph (block-parent-hash
                         (block-ext-block (car b*)))])
              (sha256-hash
                (list pph
                  (hash-block
                    (block-ext-block (car b*))))))]))
  
  (define (well-formed-blockchain? b*)
    (verifying 'well-formed-blockchain? b*
      (or (and (null? (cdr b*))
               (verify (eq? (car b*) genesis-block-ext)))
          (verifying 'block [b (block-ext-block (car b*))]
            (and (verify (block? b))
                 (verify (bytevector=?
                           (block-parent-hash b)
                           (hash-blockchain (cdr b*))))
                 (verify (> (block-epoch-number b)
                           (block-epoch-number (block-ext-block (cadr b*)))))
                 ;; TODO: check leader validity? (we didn't record the proposer's pid)
                 (well-formed-blockchain? (cdr b*)))))))

  ;; The paper does not specify transaction content, but we will need
  ;; something for testing. This format stores the pid of a client,
  ;; the timestamp of creation, and a tip amount.
  ;; (define-record-type transaction
  ;;   (nongenerative)
  ;;   (fields pid created tip))
  ;; (define (well-formed-transaction? x)
  ;;   (and (transaction? x)
  ;;        (integer? (transaction-pid x))
  ;;        (nonnegative? (transaction-pid x))
  ;;        (nonnegative? (transaction-tip x))))
  ;; (define (tx<? a b) (< (transaction-tip a) (transaction-tip b)))
  ;; (define (random-transaction n)
  ;;   (make-transaction (self) (global-time) (random n)))

  (define (well-formed-transaction? x) (number? x))

  ;; ------------------------------------------------------------------
  (define genesis-block (make-block 0 bot bot))
  (define genesis-block-ext (make-block-ext genesis-block))
  
  ;; ------------------------------------------------------------------
  ;; Signed protocol messages
  (define-datatype Message
    (Propose b)
    (Vote b)
    )

  ;; Similation control messages
  (define-datatype Control
    (Stop)
    (Epoch e)
    )
  
  (define (ht-add! label ht k v)
    (let ([len (vector-length (hashtable-keys ht))])
      (hashtable-set! ht k v)
      (bugme label (format "~a -> ~a on key ~s"
                     len
                     (vector-length (hashtable-keys ht))
                     (if (bytevector? k)
                         (hash-bytevector k)
                         k)))))

  (define emitted-db (make-eqv-hashtable))
  
  (define (node)
    (define sk #f)
    (define longest-notarized-length 1)
    (define longest-notarized-chains (list (list genesis-block-ext)))
    (define (check-for-longest-chain! chain)
      (when (chain-notarized? chain)
        (let ([len (length chain)])
          (emit-finalized! chain len)
          (cond
            [(= len longest-notarized-length)
             (bugme 'new-co-longest chain)
             (set! longest-notarized-chains
               (cons chain longest-notarized-chains))]
            [(> len longest-notarized-length)
             (bugme 'new-longest chain)
             (set! longest-notarized-length len)
             (set! longest-notarized-chains
               (list chain))]))))
    (define emit-finalized!
      (let ([cursor 0]
            [txs (lambda (b)
                   (block-txs
                     (block-ext-block b)))])
        (lambda (chain len)
          (let ([cell (hashtable-cell emitted-db (self) '())])
            ;; cddr chain below is safe because every chain reaching
            ;; this point has both the genesis block and one newly
            ;; notarized block.
            (verify (> len 1))
            (let-values ([(newly-final _) (take (cddr chain) (- len 3 cursor))])
              (unless (null? newly-final)
                (bugme `(at ,cursor) `(emit-finalized! ,(map txs chain) ,len))
                (set-cdr! cell
                  (append (bugme 'newly-final (map txs newly-final))
                    (cdr cell)))
                (set! cursor (bugme 'new-cursor (- len 3)))))))))
                
    (define orphaned-blocks '())
    ;; The block-ext-db encodes orphans as single-element chains.
    (define block-ext-db (make-bytevector-hashtable))
    (define (orphan? chain)
      (and (null? (cdr chain))
           (not (eq? (car chain) genesis-block-ext)))) ;; block-hash -> (block-ext, ..., genesis)
    (define (un-orphan! block-ext chain)
      (assert (list? chain))
      (set! orphaned-blocks (remq block-ext orphaned-blocks))
      (let ([chain (block-cons block-ext chain)])
        (hashtable-set! block-ext-db (hash-block-ext block-ext) chain)
        (check-for-longest-chain! chain)))
    (define chain-db (make-bytevector-hashtable)) ;; chain-hash -> chain
    (define (do-propose e)
      (let ([parent
              (list-ref longest-notarized-chains
                (random (length longest-notarized-chains)))])
        (assert (list? parent))
        (broadcast/me
          (sign-message sk
            (Propose
              (if (zero? (random 4))
                  (make-block e (list 'bogus)  parent)
                  (make-block e (list (+ (self) (global-time)))  parent)))))))
    (define (do-vote b)
      (broadcast/me
        (sign-message sk
          (Vote b))))
    (define (add-vote! block-ext sig)
      (unless (block-ext-notarized? block-ext)
        (let ([votes (block-ext-votes block-ext)])
          (hashtable-set! votes sig #t)
          (bugme 'add-vote! (format "~a signed vote for ~a" (mod (u8-bytevector->integer sig) 1000000) block-ext))
          (bugme 'add-vote! (format "~a votes for ~a"
                              (vector-length (hashtable-keys votes))
                              block-ext))
          (when (quorum? (vector-length (hashtable-keys votes)))
            (bugme 'add-vote! (format "quorum on epoch ~a" (block-epoch-number (block-ext-block block-ext))))
            (block-ext-notarized?-set! block-ext #t)))))
    (define highest-proposal-per-process (make-eqv-hashtable))
    (define (get-highest-proposal p)
      (cond
        [(hashtable-ref highest-proposal-per-process p #f) => identity]
        [else
          (hashtable-set! highest-proposal-per-process p 0)
          0]))
    (define (quorum? n)
      (>= n (/ (* 2 (length (cohort))) 3.0)))
    (define (intern-block block) ;; block -> chain
      (assert (block? block))
      (cond
        [(hashtable-ref block-ext-db (hash-block block) #f) =>
         (lambda (x) x)]
        [else
          (let ([block-ext (make-block-ext block)])
            (cond
              ;; See if the parent chain is known
              [(hashtable-ref chain-db (block-parent-hash block) #f) =>
               (lambda (ls)
                 (assert (list? ls))
                 (let* ([chain (block-cons block-ext ls)]
                        [chain-hash (hash-blockchain chain)])
                   (hashtable-set! block-ext-db (hash-block block) chain)
                   (hashtable-set! chain-db chain-hash chain)
                   ;; Check whether this new chain un-orphans any blocks.
                   (for-each
                     (lambda (b)
                       (when (bytevector=? (block-parent-hash (block-ext-block b)) chain-hash)
                         (un-orphan! b chain)))
                     orphaned-blocks)
                   ;; return the chain
                   chain))]
              ;; Remember as an orphan block
              [else
                (let ([chain (list block-ext)])
                  (hashtable-set! block-ext-db (hash-block block) chain)
                  (set! orphaned-blocks (cons block-ext orphaned-blocks))
                  chain)]))]))
    (spawn "p"
      (let* ([keys (create-key-pair)]
             [_sk (car keys)]
             [pk (cdr keys)])
        (set! sk _sk)
        (cohort (cons (cons (self) pk) (cohort))))
      (let ([root-chain (list genesis-block-ext)])
        (hashtable-set! chain-db (hash-blockchain root-chain) root-chain))
      (let always ()
        (handle-message (m any?)
          (cond
            [(Control? m)
             (Control-case m
               ;; ----------------------
               [(Stop) (halt)]
               ;; ----------------------
               [(Epoch e)
                (bugme 'epoch e)
                (when (leader? (self) e)
                  (bugme 'leader e)
                  (do-propose e))
                (always)])]
            [(signed-message? m)
             (let ([vm (verify-signed-message m)])
               (when (Message? vm)
                 (Message-case vm
                   ;; --------------------------------------------
                   [(Propose b)
                    (bugme 'proposal `(,(sender) ,b))
                    (when (well-formed-block? b)
                      ;; “Every player votes for the first proposal
                      ;; they see from the epoch’s leader, as long as
                      ;; the proposed block extends from (one of) the
                      ;; longest notarized chain(s) that the voter has
                      ;; seen. A vote is a signature on the proposed
                      ;; block.” ([Chan and Shi, 2020, p. 2])
                      (when (and (leader? (sender) (block-epoch-number b))
                                 (> (block-epoch-number b) (get-highest-proposal (sender))))
                        (do-vote b)))]
                   ;; --------------------------------------------
                   [(Vote b)
                    (bugme 'vote `(,(sender) ,b))
                    (when (well-formed-block? b)
                      ;; “When a block gains votes from at least 2n/3
                      ;; distinct players, it becomes notarized. A chain
                      ;; is notarized if its constituent blocks are all
                      ;; notarized.” ([Chan and Shi, 2020, p. 2])
                      (let* ([chain (intern-block b)]
                             [block-ext (car chain)])
                        (unless (block-ext-notarized? block-ext)
                          (add-vote! block-ext (signed-message-sigma m))
                          (when (block-ext-notarized? block-ext) ;; edge detect
                            (bugme 'notarized block-ext)
                            ;; Bookkeeping
                            (for-each
                              (lambda (b)
                                (block-ext-unnotarized-ancestors-set! b
                                  (remv block-ext
                                    (block-ext-unnotarized-ancestors b))))
                              (block-ext-beneficiaries block-ext))
                            ;; Maybe update longest chain
                            (check-for-longest-chain! chain)))))])))
             (always)]
            [else (always)])))))
  
  
  ;; ------------------------------------------------------------------
  (define (run-tests)
    #;(parameterize ([cohort '(a b c d)])
      (verifying 'leader-election [l (leader 3)]
        (and
          (verify (symbol? l))
          (verify (member l (cohort))))))
    #;(let ()
      (define null-chain (list genesis-block-ext))
      (define c1 (block-cons 1 '() null-chain))
      (define c2 (block-cons 2 '() c1))
      (define c3 (block-cons 4 '() c2))
      (define c4 (block-cons 6 '() c3))
      (verifying 'c4 c4
        (well-formed-blockchain? null-chain)
        (well-formed-blockchain? c1)
        (well-formed-blockchain? c2)
        (well-formed-blockchain? c3)
        (well-formed-blockchain? c4)
        )
      )
    (call-with-output-file "streamlet.puml"
      (lambda (p)
        (with-event-processor (write-plantUML p)
          (with-scheduler (event-handler (lambda (x) x))
            (spawn "t"
              (set-timer! 100 'tick)
              (let loop ([epoch 1])
                (handle-message (m any?)
                  (cond
                    [(eq? m 'tick)
                     (broadcast (Epoch epoch))
                     (set-timer! 2000 'tick) ;; 2000 required to avoid contention
                     (loop (add1 epoch))]
                    [(Control? m)
                     (Control-case m
                       [(Stop) (halt)]
                       [else (loop epoch)])]
                    [else (loop epoch)]))))
            (node) (node) (node)
            (spawn "stopper"
              (set-timer! 50000 'stop)
              (handle-message (m (exactly? 'stop))
                (broadcast (Stop))
                (halt)))
            (spawn "observer"
              (let loop ()
                (handle-message (m any?)
                  (cond
                    [(equal? m (Stop)) (set-timer! 300 'report) (loop)]
                    [(eq? m 'report)
                     (let-values ([(keys vals) (hashtable-entries emitted-db)])
                       (vector-for-each
                         (lambda (k v)
                           (printf "<<~a>>" k)
                           (for-each
                             (lambda (sublist)
                               (for-each
                                 (lambda (tx)
                                   (display " ")
                                   (write tx))
                                 sublist))
                             (reverse v))
                           (newline))
                         keys vals)
                       (newline))
                     (halt)]
                    [else (loop)]))))
            )))
      'truncate)
    #t)
  

  ;; ------------------------------------------------------------------

  (record-writer (type-descriptor block)
    (lambda (r p wr)
      (display "#block<" p)
      (wr (block-epoch-number r) p)
      (display " " p)
      (wr (block-txs r) p)
      (display " " p)
      (display-pretty-bytes (block-parent-hash r) p)
      (display ">" p)
      ))

  (record-writer (type-descriptor block-ext)
    (lambda (r p wr)
      (display "#block-ext<" p)
      (wr (block-ext-block r) p)
      (display ">" p)))
  
  
  ) ;; library
;;; ------------------------------------------------------------------------

