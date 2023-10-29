;;; ------------------------------------------------------------------------
;;;                                  Copyright 2023, Input Output Hong Kong
(library (consensus lib leader-election)
  (export cohort leader leader? lookup-pk)
  (import
    (chezscheme)
    (consensus lib common)
    (slib openssl crypto)
    (slib utils))

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
          (length (cohort)))))

    (define (leader? pid h)
      (= pid (car (leader h))))

    (define (lookup-pk pid)
      (cond
        [(assoc pid (cohort)) => cdr]
        [else #f]))
    
    ) ;; library
;;; ------------------------------------------------------------------------

