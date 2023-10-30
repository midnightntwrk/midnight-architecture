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
    #;(rename (slib merkle)
    [merkle-proof compute-merkle-proof])
    (slib datatype)
    (slib utils))
  
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

    ;; A block-ext is like an extension table for a SQL table of blocks
  ;; -- it holds extra data for each block.  Each block-ext represents
  ;; the head of a chain of blocks.  I.e., a blockchain is still a
  ;; list of blocks, not block-exts, but every block-ext knows the
  ;; full chain of ancestor blocks for its corresponding block.  These
  ;; chains (lists of blocks) benefit from tail sharing.  I.e., every
  ;; block is instantiated only once in each process.  We maintain a
  ;; chain-db for looking up a chain by its hash.
  ;;
  ;; We could do this differently.  Still have the chain-db hashtable,
  ;; but what it maps to is wrapped blocks, where the wrapper holds
  ;; all the block-ext data.  This obviates the need to 'join' against
  ;; a secondary block-ext table.

  ;; A notarized block-ext with no unnotarized-ancestors is the head
  ;; of a notarized chain.
  ;;
  ;; When we create a block-ext b, we walk the whole list of blocks in
  ;; its parent chain and, for each unnotarized corresponding
  ;; block-ext a, we (1) add the new b to the beneficiaries of a, and
  ;; (2) we add a to the unnotarized-ancestors of a. NB: we can stop
  ;; the loop as soon as we hit a block-ext with no
  ;; unnotarized-ancestors.
  ;;
  ;; Whenever a block-ext a becomes notarized itself, we (1) update
  ;; all the beneficiaries' unnotarized-ancestors, deleting a, and (2)
  ;; we set its beneficiaries list to '().  If this causes a block-ext
  ;; to become the head of the longest notarized chain, we promote it
  ;; to the set of longest-notarized-chains and update
  ;; longest-notarized-length to the length field from the block-ext.
  ;;
  ;; We should also prune defunct block-exts.  A block-ext is defunct
  ;; when there exists a longest-notarized-chain that does not include
  ;; the block-ext's corresponding block. Even notarized blocks can
  ;; become defunct.
  (define-record-type block-ext
    (nongenerative)
    (fields
      block ;; the block for which this is the ext
      parent-chain ;; list of blocks (the block holds the hash of this chain)
      chain-length
      (mutable votes) ;; signatures
      notarized?
      (mutable unnotarized-ancestors) ;; blocks
      (mutable beneficiaries) ;; block-exts
      ))

  ;; This is an important operation, with side effects, that adds a
  ;; new block-ext to a chain and updates all the mutable pointers
  ;; required to track notarizations.
  (define block-cons
    (case-lambda
      [(epoch-number txs parent-chain)
       (block-cons (make-block epoch-number txs parent-chain)
         parent-chain)]
      [(block parent-chain)
       (let* ([block-ext
                (make-block-ext block parent-chain (add1 (length parent-chain))
                  '() #f '() '())]
              [ls (cons block-ext parent-chain)])
         (for-each
           (lambda (b)
             (unless (block-ext-notarized? b)
               (block-ext-beneficiaries-set! b
                 (cons block-ext
                   (block-ext-beneficiaries b)))
               (block-ext-unnotarized-ancestors-set! block-ext
                 (cons b
                   (block-ext-unnotarized-ancestors b)))
               ))
           ls)
         ls)]))
             

  ;; When we hash a block, we hash just the protocol's notion of the
  ;; block, not the full block-ext record.
  (define (hash-block b)
    (assert (block-ext? b))
    (sha256-hash
      (list (block->bytevector
              (block-ext-block b)))))

  ;; Blockchain blocks are a descending linked list (b_h, ..., b_0)
  (define (blockchain? x) (and (list? x) (andmap block-ext? x)))

  ;; Optimistically hash a chain assuming the shape (b_h, ..., b_0) by
  ;; hashing together the block hash of b_h with its parent hash.
  ;; This operation relies on just the first element of the list.  To
  ;; verify a well-formed blockchain, call `well-formed-blockchain?`
  (define (hash-blockchain b*)
    (verifying 'hash-blockchain b*
      (verify (andmap block-ext? b*)))
    (cond
      [(null? b*) (sha256-hash '())]
      [(= 1 (length b*))
       (assert (eq? (car b*) genesis-block-ext))
       (hash-block genesis-block-ext)]
      [else (let ([pph (block-parent-hash
                         (block-ext-block (car b*)))])
              (sha256-hash
                (list pph
                  (hash-block
                    (car b*)))))]))
  
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
  (define-record-type transaction
    (nongenerative)
    (fields pid created tip))
  (define (well-formed-transaction? x)
    (and (transaction? x)
         (integer? (transaction-pid x))
         (nonnegative? (transaction-pid x))
         (nonnegative? (transaction-tip x))))
  (define (tx<? a b) (< (transaction-tip a) (transaction-tip b)))
  (define (random-transaction n)
    (make-transaction (self) (global-time) (random n)))


  ;; ------------------------------------------------------------------
  (define genesis-block
    (make-block 0 bot bot))
  (define genesis-block-ext
    (make-block-ext genesis-block '() 1 '() #t '() '()))
  
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
  
  ;; ------------------------------------------------------------------
  ;; Chain Hashtable
  ;;
  ;; When we receive messages with blocks, the blocks include the
  ;; parent hash. We require a way of looking up the parent chain from
  ;; the given hash. A blockchain is a list of block-ext nodes, and we
  ;; have the function hash-blockchain to compute the chain's
  ;; hash. Since this is a collision-resistant hash, we treat the hash
  ;; as the identity for equality checks.
  ;;
  ;; NB: There is some ineffiency here from recomputing
  ;; hash-blockchain, but the function is a constant-time overhead we
  ;; won't worry about here.
  (define (make-chain-hashtable)
    (make-hashtable
      hash-blockchain
      (lambda (x y) (bytevector=? (hash-blockchain x) (hash-blockchain y)))))
  
  
  (define (node)
    (define longest-notarized-length 1)
    (define longest-notarized-chains (list genesis-block-ext))
    (define block-ext-db (make-eqv-hashtable))
    (define chain-db (make-chain-hashtable))
    (define (do-propose e)
      (let ([parent
              (list-ref longest-notarized-chains
                (random (length longest-notarized-chains)))])
        (broadcast
          (sign-message
            (Propose
              (make-block e '() parent))))))
    (spawn "p"
      (let always ()
        (handle-message (m any?)
          (cond
            [(Control? m)
             (Control-case m
               [(Stop) (halt)]
               [(Epoch e)
                (when (leader? (self) e)
                  (do-propose e))
                (always)])]
            [(signed-message? m)
             (let ([vm (verify-signed-message m)])
               (when (Message? vm)
                 (Message-case vm
                   [(Propose b)
                    (when (leader? (sender) (block-epoch-number b))
                      ;; “Every player votes for the first proposal
                      ;; they see from the epoch’s leader, as long as
                      ;; the proposed block extends from (one of) the
                      ;; longest notarized chain(s) that the voter has
                      ;; seen. A vote is a signature on the proposed
                      ;; block.” ([Chan and Shi, 2020, p. 2])
                       ===)]
                   [(Vote b)
                    ;; “When a block gains votes from at least 2n/3
                    ;; distinct players, it becomes notarized. A chain
                    ;; is notarized if its constituent blocks are all
                    ;; notarized.” ([Chan and Shi, 2020, p. 2])
                    ===])))
             (always)]
            [else (always)])))))
  
  
  ;; ------------------------------------------------------------------
  (define (run-tests)
    (parameterize ([cohort '(a b c d)])
      (verifying 'leader-election [l (leader 3)]
        (and
          (verify (symbol? l))
          (verify (member l (cohort)))))
      (let ()
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
            (with-scheduler (event-handler (trace-lambda handler (x) x))
              ;; (producer) (producer) (producer)
              (spawn "stopper"
                (set-timer! 3000 'stop)
                (handle-message (m (exactly? 'stop))
                  (broadcast (Stop))
                  (halt)))
              (spawn "t"
                (set-timer! 100 'tick)
                (let loop ([epoch 1])
                  (handle-message (m any?)
                    (cond
                      [(eq? m 'tick)
                       (broadcast `(epoch ,epoch))
                       (set-timer! 100 'tick)
                       (loop (add1 epoch))]
                      [(Control? m)
                       (Control-case m
                         [(Stop) (halt)]
                         [else (loop epoch)])]
                      [else (loop epoch)]))))
              )))
        'truncate)
      #t))
  

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

