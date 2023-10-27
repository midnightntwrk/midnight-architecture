;;; ------------------------------------------------------------------------
;;;                                  Copyright 2023, Input Output Hong Kong
(library (simplex)
  (export run-tests)
  (import
    (chezscheme)
    (scheme-actors yassam)
    (slib openssl crypto)
    ;;(slib faux-ppk)
    #;(rename (slib merkle)
    [merkle-proof compute-merkle-proof])
    (slib datatype)
    (slib utils))

  ;; ---------------------------------------------------------
  ;; Utilities
  (define (exactly? x) (lambda (y) (equal? y x)))
  (define (not-implemented . context) (errorf 'not-implemented "~a" context))
  (define === 'not-implemented)
  (define (bug label val)
    (printf "BUG  ~a => ~s\n" label val)
    val)
  (define (flatten x)
    (cond
      [(null? x) '()]
      [(list? x) (append (flatten (car x)) (flatten (cdr x)))]
      [else (list x)]))
  (define (occurences x ls)
    (cond
      [(null? ls) 0]
      [(eqv? (car ls) x) (add1 (occurences x (cdr ls)))]
      [else (occurences x (cdr ls))]))
  (define bot '⊥)
  (define (bot? x) (eq? x bot))
  (define make-string-hashtable
    (lambda ()
      (make-hashtable string-hash equal?)))
  (define (identity x) x)
  (define (take ls n)
    (let loop ([i 0] [head '()] [tail ls])
      (if (or (= i n) (null? tail))
          (values (reverse head) tail)
          (loop (add1 i) (cons (car tail) head) (cdr tail)))))

  (define (verify who label val)
    (or val
        (printf "xFAIL ~a: ~a\n" who label)
        #f))
  (define (fail who pred val)
    (printf "FAIL ~a: (~a ~a)\n" who pred val)
    #f)
  (define-syntax verify-all
    (lambda (x)
      (syntax-case x ()
        [(_ who exp pred ...)
         #'(call/cc
             (lambda (k)
               (let ([x (with-exception-handler
                          (lambda (e)
                            (if (error? e)
                                (begin
                                  (printf "ERR ~a " who)
                                  (display-condition e)
                                  (raise e))
                                (raise e)))
                          (lambda () exp))])
                 (and
                   (with-exception-handler
                     (lambda (e)
                       (if (error? e)
                           (begin
                             (printf "ERR ~a ~a " who 'pred)
                             (display-condition e)
                             (raise e))
                           (raise e)))
                     (lambda () (or (pred x) (fail who 'pred x))))
                   ...))))])))
  (define-syntax verify-any
    (lambda (x)
      (syntax-case x ()
        [(_ who exp pred ...)
         #'(call/cc
             (lambda (k)
               (let ([x (with-exception-handler
                          (lambda (e)
                            (if (error? e)
                                (begin
                                  (printf "ERR ~a " who)
                                  (display-condition e)
                                  (raise e))
                                (raise e)))
                          (lambda () exp))])
                 (or
                   (with-exception-handler
                     (lambda (e)
                       (if (error? e)
                           (begin
                             (printf "ERR ~a ~a " who 'pred)
                             (display-condition e)
                             (raise e))
                           (raise e)))
                     (lambda () (or (pred x) (fail who 'pred x))))
                   ...))))])))

  ;; ---------------------------------------------------------
  ;; Data structures for state and messages

  (define-record-type block
    (nongenerative)
    (fields h parent-chain-hash txs)
    (protocol
      (lambda (new)
        (lambda (h parent-chain txs) ;; must specify parent chain, not hash
          (cond
            ;; Genesis block
            [(= h 0) (new 0 (sha256-hash '()) '())]
            ;; Dummy block
            [(bot? parent-chain) (new h bot bot)]
            ;; Ordinary block
            [else (new h (hash-blockchain parent-chain) txs)])))))
  (define (block->bytevector b)
    (let ([tx (make-transcoder (latin-1-codec) (eol-style lf)
                (error-handling-mode replace))])
      (call-with-bytevector-output-port
        (lambda (p)
          (fprintf p "block ~s ~s ~s"
            (block-h b)
            (block-parent-chain-hash b)
            (block-txs b)))
        tx)))
  (define-who (hash-block b)
    (sha256-hash (list (block->bytevector b))))
  (define-who (well-formed-block? b)
    ;; Validation of the parent reference happens in context, using
    ;; `well-formed-blockchain?`.
    (and (verify-all who b block?)
         (verify-all who (block-h b) nonnegative?)
         (verify-all who (block-parent-chain-hash b) bytevector?)
         (let ([txs (block-txs b)])
           (or (bot? txs)
               (and
                 (verify who 'list-txs? (list? txs))
                 (verify who 'wff-txs? (andmap well-formed-transaction? txs)))))))
  (define (make-dummy-block h)
    (make-block h bot bot))
  (define (dummy-block? b)
    (bot? (block-parent-chain-hash b)))

  (define-record-type blockchain
    (nongenerative)
    (fields blocks))
  (define (hash-blockchain x)
    ;; Bit of a hack here, but let's reuse `well-formed-blockchain?`
    ;; as it already computes the cumulative hash.
    (or 
      (well-formed-blockchain? x)
      (errorf 'hash-blockchain "malformed chain ~s" x)))
  (define (well-formed-blockchain? x)
    (and (blockchain? x)
         (list? (blockchain-blocks x))
         (verify 'well-formed-blockchain? 'all-blocks? (andmap block? (blockchain-blocks x)))
         ;;(andmap well-formed-block? (blockchain-blocks x))
         ;; Verify the parent hashes form the given block sequence.
         (let ([b0 (car (blockchain-blocks x))])
           (and
             ;; Must start with genesis block
             (eq? b0 genesis-block)
             ;; Every block must correctly represent its parent hash
             ;; by looping forward from genesis, calculating the
             ;; cumulative hash for each prefix of the given chain and
             ;; comparing to the parent-chain-hash of the block that
             ;; extends the prefix.
             (let loop ([h 1]
                        [parent b0]
                        [prefix-hash (hash-block b0)] ;; base case
                        [suffix (cdr (blockchain-blocks x))])
               (or (and (null? suffix)
                        prefix-hash) ;; return hash to aid `hash-blockchain`
                   (let ([b (car suffix)])
                     (and (= (block-h b) h)
                          (or
                            ;; A dummy block does not point to a specific parent
                            (dummy-block? b)
                            ;; Any other block must be checked
                            (bytevector=? prefix-hash (block-parent-chain-hash b)))
                          ;; Recur
                          (loop (+ h 1) b
                            (sha256-hash (list prefix-hash (hash-block b)))
                            (cdr suffix))))))))))

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

  ;; Putting this quite late to ensure all required definitions are in
  ;; place.
  (define genesis-block (make-block 0 (sha256-hash '()) '()))

  

  ;; NB: could we replace block b with its hash?
  (define-record-type unsigned-vote
    (nongenerative)
    ;; h = height (0-based)
    ;; b = block
    (fields h b))

  (define-record-type notarized-blockchain
    (nongenerative)
    ;; blocks = (b_h, ..., b_0)
    ;; S = ((<vote, 0, b_0>_p ...) ... (<vote, h, b_h>_p' ...))
    ;;      `... quorum of p ...'       `... quorum of p' ...'
    (fields blocks S))

  (define-record-type unsigned-finalization
    (nongenerative)
    (fields h))

  (define-record-type finalized-blockchain
    (nongenerative)
    ;; nbc = a notarized-blockchain of height h
    ;; F = set of signed finalization messages for hight h
    (fields nbc F))

  ;; ---------------------------------------------------------
  ;; Message signing and verifying
  (define-record-type signed-message
    (nongenerative)
    ;; m = message
    ;; sigma = signature (a signed bytevector of the msg contents)
    (fields m sigma)
    (protocol
      (lambda (new)
        (lambda (sk m)
          (let ([bv (message->bytevector m)])
            (new m (sha256-sign (list bv) sk)))))))
  (define sign-message make-signed-message)
  (define (message->bytevector m)
    (let ([tx (make-transcoder (latin-1-codec) (eol-style lf)
                (error-handling-mode replace))])
      (call-with-bytevector-output-port
        (lambda (p) (write m p))
        tx)))
  
  (define (run-tests)
    (define keys (create-key-pair))
    (define sk (car keys))
    (define pk (cdr keys))
    (define m '(hello world))
    (define sm (sign-message sk m))
    (printf "signed: ~s\n" sm)
    (unless (verify-message sm pk) (errorf 'verify "failed"))
    (list
      (random-transaction 300)
      (random-transaction 300)
      (random-transaction 300))
    #;(bug 'block?
      (well-formed-block? 'not-a-block))
    (bug 'genesis-block genesis-block)
    (let ()
      (define b0 genesis-block)
      (define c0 (make-blockchain (list b0)))
      (define b1 (make-block 1 c0 '()))
      (define b2 (make-block 2 (make-blockchain (list b0 b1)) '()))
      (define d2 (make-dummy-block 2))
      (define d3 (make-dummy-block 3))
      (define b4 (make-block 4 (make-blockchain (list b0 b1 d2 d3)) '()))
      (assert (well-formed-block? b4))
      ;;33
      )
    #;(call-with-output-file "simplex.puml"
      (lambda (p)
        (with-event-processor (write-plantUML p)
          (with-scheduler (event-handler (trace-lambda handler (x) x))
            (producer) (producer) (producer)
            (spawn "stopper"
              (set-timer! 3000 'stop)
              (handle-message (m (exactly? 'stop))
                (broadcast 'stop)
                (halt)))
            )))
      'truncate)
    mempool
    )



  ;; ---------------------------------------------------------
  ;; Leader election

  ;; `each iteration h has a pre-determined block proposer or leader Lh ∈
  ;; [n] that is randomly chosen ahead of time; this is referred to as a
  ;; random leader election oracle`

  ;; This function takes a set of pids (a cohort) and a block-height
  ;; h, and returns the designated leader for that block height from
  ;; within that cohort.
  (define leader-oracle
    (let ([cohorts (make-string-hashtable)])
      (lambda (pids h)
        (let ([cohort-key (format "~s" pids)])
          (let ([cohort-leaders
                  (cond
                    [(hashtable-ref cohorts cohort-key #f) => identity]
                    [else (let ([ht (make-eqv-hashtable)])
                            (hashtable-set! cohorts cohort-key ht)
                            ht)])])
            (cond
              [(hashtable-ref cohort-leaders h #f) => identity]
              [else (let ([leader 
                            (list-ref pids
                              (random (length pids)))])
                      (hashtable-set! cohort-leaders h leader)
                      leader)]))))))

  (define (slot-leader? pid h)
    (= pid (car (leader-oracle cohort))))

  ;; ---------------------------------------------------------
  ;; Message types

  (define-datatype Message
    (Propose h blocks notarization)
    (Vote h block)
    (Finalize h)
    )

  (define (well-formed-message? m)
    (Message-case m
      [(Propose h blocks notarization)
       (and
         (= (+ h 1) (length blocks))
         (well-formed-blockchain? (make-blockchain blocks))
         (andmap valid-block-notarization?
           (reverse notarization)
           (cdr (reverse blocks))))]
      [(Vote h block) (= h (block-h block))]
      [(Finalize h) ===]
      ))

  (define (valid-block-notarization? b votes)
    (and (list? votes)
         (andmap signed-message? votes)
         ===
         ;; - verify signatures
         ;; - ensure uniqueness
         ;; - ensure 2/3 quourm
         ;; - ensure b is vote.b and its height is vote.h
         ))


  (define (propose sk h blocks notarization)
    (broadcast
      (sign-message sk
        (Propose h blocks notarization))))

  (define (vote sk h block)
    (broadcast
      (sign-message sk
        (Vote h block))))

  (define (finalize sk h)
    (broadcast
      (sign-message sk
        (Finalize h))))

  ;; ------------------------------------------------------------------
  ;; The "mempool" of transactions waiting to be published.
  (define mempool '())
  (define (pull-from-mempool n)
    (let-values ([(head tail) (take mempool n)])
      (set! mempool tail)
      head))
    
  ;; ------------------------------------------------------------------
  ;; The cohort of BFT participants
  ;; A set of pairs (pid . pk)
  (define cohort '())
  
  (define verify-message
    (case-lambda
      [(sm pk) (let ([bv (message->bytevector (signed-message-m sm))])
                 (sha256-verify (list bv) (signed-message-sigma sm) pk))]
      [(sm) (cond
              [(assoc (sender) cohort) =>
               (lambda (pr)
                 (verify-message sm (cdr pr)))]
              [else (declaim "invalid sender ~s" (sender))])]))

  ;; ------------------------------------------------------------------
  ;; Actors

  ;; Producers represent clients sendning requests to consensus.
  (define (producer)
    (spawn "produce"
      (set-timer! 0 'start)
      (let loop ()
        (handle-message (m any?)
          (if (eq? m 'stop)
              (halt)  ;; anyone can stop the system by broadcasting 'stop
              (begin
                (set-timer! (* 100 (random 10)) 'continue)
                (let post ([i (add1 (random 20))])
                  (unless (zero? i)
                    (let ([tx (random-transaction 100)])
                      (set! mempool
                        (sort tx<? (cons tx mempool))))
                    (post (- i 1))))
                (loop)))))))
 
  ;; (define process
  ;;   (lambda ()
  ;;     (spawn "p"
  ;;       (let* ([keys (create-key-pair)]
  ;;              [sk (car keys)]
  ;;              [pk (cdr keys)])
  ;;         (set! cohort (cons (cons (self) pk) cohort)))
  ;;       (set-timer 100 'start)
  ;;       (handle-message (m (exactly? 'start))
  ;;         (let loop ([h 0])
  ;;           (if (slot-leader? (self) h)
  ;;               (let* ([chain (longest-notarized-chain)]
  ;;                      [txs (pull-from-mempool 10)] ;; "every pending tx not already in the chain"
  ;;                      ;;
  ;;                      ;; To check inclusion, we might as well have
  ;;                      ;; each node induce a Merkle tree per
  ;;                      ;; notarizated blockchain, containing all
  ;;                      ;; transactions in sequence.  Then we filter
  ;;                      ;; the mempool using Merkle inclusion.
  ;;                      ;;
  ;;                      [parent (car (notarized-blockchain-blocks chain))]
  ;;                      [S (notarized-blockchain-S chain)]
  ;;                      [block (make-block h parent txs)])
  ;;                 (propose sk h
  ;;                   (make-notarized-blockchain 
  ;;                     (cons block (notarized-blockchain-blocks chain))
  ;;                     S))
                      
  ;;                   notarization)
                  
  ;;           (handle-message

  ;; (define (consumer)
  ;;   (spawn "consume"
  ;;     (handle-message (m Message?)
        
        
  
  ;; ------------------------------------------------------------------
  ;; Pretty printing
  ;;
  ;; NB: record-writer updates are expressions, and must therefore
  ;; be listed after all definitions in the library.

  
  (define (bv->s bv)
    (let* ([ls (map abs (bytevector->s8-list bv))]
           [len (length ls)])
      (call-with-string-output-port
        (lambda (p)
          (let loop ([i 0])
            (when (< i len)
              (fprintf p "~x" (list-ref ls i))
              (loop (add1 i))))))))
  
  (record-writer (type-descriptor signed-message)
    (lambda (r p wr)
      (let* ([str (bv->s (signed-message-sigma r))]
             [len (string-length str)])
        (display "#signed<" p)
        (wr (signed-message-m r) p)
        (display " ")
        (display (substring str (- len (+ 66 8)) (- len 66)) p)
        (display ">" p)
      )))

  (record-writer (type-descriptor transaction)
    (lambda (r p wr)
      (display "#tx<" p)
      (display (transaction-pid r) p)
      (display " " p)
      (display (transaction-created r) p)
      (display " " p)
      (display (transaction-tip r) p)
      (display ">" p)))
    

  ) ;; library
;;; ------------------------------------------------------------------------
