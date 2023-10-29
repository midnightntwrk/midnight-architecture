;;; ------------------------------------------------------------------------
;;;                                  Copyright 2023, Input Output Hong Kong
(library (consensus lib verify)
  (export
    verifying verify
    )
  (import
    (chezscheme))

  (define verifying-stack (make-parameter '()))
  (define (fail-proc label . ?condition)
    (if (null? (verifying-stack))
        (if (null? ?condition)
              (printf "[FAIL ] ~a\n" label)
              (begin
                (printf "[ERROR] ~a => " label)
                (display-condition (car ?condition))
                (newline)))
        (let* ([pr (car (verifying-stack))]
               [who (car pr)]
               [var (cadr pr)]
               [val (cddr pr)])
          (verifying-stack (cdr (verifying-stack)))
          (if (null? ?condition)
              (printf "[FAIL ] ~a: ~a where ~a = ~s\n" who label var val)
              (begin
                (printf "[ERROR] ~a: ~a where ~a = ~s => " who label var val)
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

) ;; library
;;; ------------------------------------------------------------------------
