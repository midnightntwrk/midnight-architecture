;;; ------------------------------------------------------------------------
;;;                                  Copyright 2023, Input Output Hong Kong
(library (consensus lib common)
  (export
    identity exactly?
    not-implemented ===
    bug
    flatten occurrences take remove-duplicates
    bot bot?
    make-string-hashtable
    uint->u8-bytevector u8-bytevector->integer
    )
  (import
    (chezscheme)
    (slib openssl crypto))

  (define (identity x) x)
  (define (exactly? x) (lambda (y) (equal? y x)))
  (define (not-implemented . context) (errorf 'not-implemented "~a" context))
  (define === 'not-implemented)
  (define (bug label val)
    (printf "[DEBUG] ~a => ~s\n" label val)
    val)
  (define (flatten x)
    (cond
      [(null? x) '()]
      [(list? x) (append (flatten (car x)) (flatten (cdr x)))]
      [else (list x)]))
  (define (occurrences x ls)
    (cond
      [(null? ls) 0]
      [(eqv? (car ls) x) (add1 (occurrences x (cdr ls)))]
      [else (occurrences x (cdr ls))]))
  (define (take ls n)
    (let loop ([i 0] [head '()] [tail ls])
      (if (or (= i n) (null? tail))
          (values (reverse head) tail)
          (loop (add1 i) (cons (car tail) head) (cdr tail)))))
  (define (remove-duplicates ls)
    (cond
      [(null? ls) '()]
      [(member (car ls) (cdr ls)) (cdr ls)]
      [else (cons (car ls) (remove-duplicates (cdr ls)))]))
  (define bot '⊥)
  (define (bot? x) (eq? x bot))
  (define make-string-hashtable
    (lambda ()
      (make-hashtable string-hash equal?)))

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


  ) ;; library
;;; ------------------------------------------------------------------------

