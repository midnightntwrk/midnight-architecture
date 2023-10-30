;;; ------------------------------------------------------------------------
;;;                                  Copyright 2023, Input Output Hong Kong
(library (simplex)
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
  (define (hash-block b)
    (sha256-hash (list (block->bytevector b))))
  (define-who (well-formed-block? b)
    ;; Validation of the parent reference happens in context, using
    ;; `well-formed-blockchain?`.
    (verifying who b
      (and (verify (block? b))
           (verify (nonnegative? (block-h b)))
           (verify (bytevector? (block-parent-chain-hash b)))
           (verifying who [txs (block-txs b)]
             (or (bot? txs)
                 (and
                   (verify (list? txs))
                   (verify (andmap well-formed-transaction? txs))))))))
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
      (well-formed-blockchain? x) ;; returns cumulative hash
      (errorf 'hash-blockchain "malformed chain ~s" x)))
  (define-who (well-formed-blockchain? x)
    (verifying who x
      (and (verify (blockchain? x))
           (verify (list? (blockchain-blocks x)))
           (verify (andmap block? (blockchain-blocks x)))
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
                              (cdr suffix)))))))))))

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

  (define-record-type notarized-blockchain
    (nongenerative)
    ;; blocks = (b_h, ..., b_0)
    ;; S = ((<vote, 0, b_0>_p ...) ... (<vote, h, b_h>_p' ...))
    ;;      `... quorum of p ...'       `... quorum of p' ...'
    (fields blocks S))

  (define-record-type finalized-blockchain
    (nongenerative)
    ;; nbc = a notarized-blockchain of height h
    ;; F = set of signed finalization messages for height h
    (fields nbc F))

  
  
  (define (run-tests)
    (define keys (create-key-pair))
    (define sk (car keys))
    (define pk (cdr keys))
    (define m (Vote 0 genesis-block))
    (define sm (sign-message sk m))
    (printf "signed: ~s\n" sm)
    (unless (verify-signed-message sm pk) (errorf 'verify "failed"))
    (list
      (random-transaction 300)
      (random-transaction 300)
      (random-transaction 300))
    (begin
      (assert (verifying 'me [x -44] (verify (negative? x))))
      (assert (not (verifying 'me [x 44] (verify (negative? x)))))
      (assert (let ([x -55]) (verifying 'me x (verify (negative? x)))))
      (assert (not (let ([x 55]) (verifying 'me x (verify (negative? x))))))
      (assert (not (verify (/ 3 0))))
      )
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
      )
    (call-with-output-file "simplex.puml"
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
           ;; Every block except genesis and the latest
           ;; block needs a notarization.  Assume h blocks
           ;; have h-2 notarizations, (b1 ... bh-1).
           notarization
           (reverse (cdr (reverse (cdr blocks))))))]
      [(Vote h block) (= h (block-h block))]
      [(Finalize h) #t]
      ))

  (define (valid-block-notarization? b votes)
    (and (list? votes)
         (andmap signed-message? votes)
         ;; - verify signatures
         (andmap verify-signed-message votes)
         ;; - ensure b is vote.b and its height is vote.h
         (andmap (lambda (sm)
                   (Message-case (signed-message-m sm)
                     [(Vote h block)
                      (and
                        (eq? block b)
                        (= h (block-h b)))]
                     [else #f]))
           votes)
         ;; - ensure uniqueness
         (equal? votes (remove-duplicates votes))
         ;; - ensure 2/3 quourm
         (> (length votes) (* 2 (/ (length cohort) 3.0)))
         ))

  (define (propose! sk h blocks notarization)
    (broadcast
      (sign-message sk
        (Propose h blocks notarization))))

  (define (vote! sk h block)
    (broadcast
      (sign-message sk
        (Vote h block))))

  (define (finalize! sk h)
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

#|

  Each process essentially maintains a database of slots, indexed by id, where
  each slot is a state machine:

  
  
  |#

  
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
  
  (record-writer (type-descriptor signed-message)
    (lambda (r p wr)
      (display "#signed<" p)
      (wr (signed-message-m r) p)
      (display " ")
      (display-pretty-bytes (signed-message-sigma r) p)
      (display ">" p)
      ))

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
