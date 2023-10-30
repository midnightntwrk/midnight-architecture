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
  
  (define (block-cons epoch-number txs parent-chain)
    (cons (make-block epoch-number txs parent-chain)
      parent-chain))

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

  (define (hash-block b)
    (sha256-hash (list (block->bytevector b))))
  
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

  ;; Blockchain blocks are a descending linked list (b_h, ..., b_0)
  (define blockchain? list?)

  ;; Optimistically hash a chain assuming the shape (b_h, ..., b_0) by
  ;; hashing together the block hash of b_h with its parent hash.
  ;; This operation relies on just the first element of the list.  To
  ;; verify a well-formed blockchain, call `well-formed-blockchain?`
  (define (hash-blockchain b*)
    (cond
      [(null? b*) (sha256-hash '())]
      [(= 1 (length b*))
       (assert (eq? (car b*) genesis-block))
       (hash-block genesis-block)]
      [else (let ([pph (block-parent-hash (car b*))])
              (sha256-hash
                (list pph (hash-block (car b*)))))]))
  
  (define (well-formed-blockchain? b*)
    (verifying 'well-formed-blockchain? b*
      (or (and (null? (cdr b*))
               (verify (eq? (car b*) genesis-block)))
          (verifying 'block [b (car b*)]
            (and (verify (bytevector=?
                           (block-parent-hash b)
                           (hash-blockchain (cdr b*))))
                 (verify (> (block-epoch-number b)
                           (block-epoch-number (cadr b*))))
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
    (define genesis-block (make-block 0 bot bot))
  ;; ------------------------------------------------------------------

  (define (run-tests)
    (parameterize ([cohort '(a b c d)])
      (verifying 'leader-election [l (leader 3)]
        (and
          (verify (symbol? l))
          (verify (member l (cohort)))))
      (let ()
        (define null-chain (list genesis-block))
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
  
  
  ) ;; library
;;; ------------------------------------------------------------------------

