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

  (define (run-tests)
    (parameterize ([cohort '(a b c d)])
      (verifying 'leader-election [l (leader 3)]
        (and
          (verify (symbol? l))
          (verify (member l (cohort))))
        #t)))
        

  
  
  ) ;; library
;;; ------------------------------------------------------------------------

