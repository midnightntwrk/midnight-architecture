;;; ------------------------------------------------------------------------
;;;                                  Copyright 2023, Input Output Hong Kong
(library (streamlet)
  (export run-tests)
  (import
    (chezscheme)
    (scheme-actors yassam)
    (slib openssl crypto)
    #;(rename (slib merkle)
       [merkle-proof compute-merkle-proof])
    (slib datatype)
    (slib utils))

  (module (leader cohort)
    (module (uint->u8-bytevector u8-bytevector->integer)
      (define (factor-256 n)
        (let loop ([n n] [ls '()])
          (if (< n 256)
              (cons n ls)
              (let ([r (remainder n 256)]
                    [d (div n 256)])
                (loop d (cons r ls))))))
      (define (uint->u8-bytevector n)
        (u8-list->bytevector (factor-256 n)))
      (define (u8-bytevector->integer bv)
        (let ([ls (bytevector->u8-list bv)])
          (let loop ([ls ls] [e (sub1 (length ls))])
            (if (null? ls)
                0
                (+ (* (car ls) (expt 256 e))
                  (loop (cdr ls) (sub1 e))))))))

    ;; The cohort of BFT participants
    ;; A set of pairs (pid . pk)
    (define cohort (make-parameter '()))

    ;; Random(?) leader oracle based on a common formulation
    ;;
    ;; “each iteration h has a pre-determined block proposer or leader
    ;; Lh ∈ [n] that is randomly chosen ahead of time; this is referred
    ;; to as a random leader election oracle [...] implemented by a
    ;; random oracle: namely, Lh := H∗(h) mod n, where H∗(·) is some
    ;; public hash function modeled as a random oracle” (Chan and Pass,
    ;; 2023, p. 9)
    (define (leader h)
      (list-ref (cohort)
        (mod 
          (u8-bytevector->integer
            (sha256-hash
              (list
                (uint->u8-bytevector h))))
          (length (cohort))))))

  (define verifying-stack (make-parameter '()))
  (define (fail-proc label . ?condition)
    (if (null? (verifying-stack))
        (if (null? ?condition)
              (printf "FAIL: ~a\n" label)
              (begin
                (printf "ERR: ~a => " label)
                (display-condition (car ?condition))
                (newline)))
        (let* ([pr (car (verifying-stack))]
               [who (car pr)]
               [var (cadr pr)]
               [val (cddr pr)])
          (verifying-stack (cdr (verifying-stack)))
          (if (null? ?condition)
              (printf "FAIL ~a: ~a where ~a = ~s\n" who label var val)
              (begin
                (printf "ERR ~a: ~a where ~a = ~s => " who label var val)
                (display-condition (car ?condition))
                (newline)))))
    #f)
  (define-syntax verifying
    (lambda (x)
      (syntax-case x ()
        [(_ who var e0 e1 ...)
         (identifier? #'var)
         #'(parameterize ([verifying-stack (cons `(,who var . ,var) (verifying-stack))])
             e0 e1 ...)]
        [(_ who [var val] e0 e1 ...)
         (identifier? #'var)
         #'(let ([var val])
             (parameterize ([verifying-stack (cons `(,who var . ,val) (verifying-stack))])
               e0 e1 ...))])))
  (define-syntax verify
    (lambda (x)
      (syntax-case x ()
        [(_ test)
         #'(call/cc
             (lambda (k)
               (let ([x (with-exception-handler
                          (lambda (e)
                            (k (fail-proc 'test e)))
                          (lambda () test))])
                 (or test
                     (fail-proc 'test)))))])))
  
  ;; ------------------------------------------------------------------

  (define (run-tests)
    (parameterize ([cohort '(a b c d)])
      (verifying 'leader-election [l (leader 3)]
        (and
          (verify (symbol? l))
          (verify (member l (cohort))))
        #t)))
        

  
  
  ) ;; library
;;; ------------------------------------------------------------------------

