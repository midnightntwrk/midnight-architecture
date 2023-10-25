;;; ------------------------------------------------------------------------
;;;                                  Copyright 2023, Input Output Hong Kong
;;; ------------------------------------------------------------------------

(library (glacier-drop)
  (export run-tests)
  (import
    (chezscheme)
    (scheme-actors yassam)
    ;; (slib openssl crypto)
    (slib faux-ppk)
    (slib datatype)
    )

  (define (exactly? x) (lambda (y) (equal? y x)))

  
  (define (run-tests)
    (call-with-output-file "glacier-drop.puml"
      (lambda (p)
        (with-event-processor (write-plantUML p)
          (with-scheduler (event-handler (trace-lambda handler (x) x))

            (define-record-type source-wallet (nongenerative) (fields pk amount))
            (define-record-type grant (nongenerative) (fields pk amount))
            (define-record-type msg:token-event (nongenerative) (fields root))
            (define-datatype das-msg
              (find-grant pk))
            (define-datatype das-reply
              (grant-not-found)
              (grant-found path amount))
        
            (define source-chain-wallets '())

            (define (compute-grants)
              (map
                (lambda (w)
                  (make-grant (source-wallet-pk w)
                    (* 10 (source-wallet-amount w))))
                source-chain-wallets))

            (define (calculate-root tree)
              (string-hash (format "~s" tree)))

            (define data-availability-service (make-parameter #f))
        
            (define (make-data-availability-service)
              (let ([grants #f])
                (spawn "das"
                  (define (await-token-event)
                    (handle-message (m msg:token-event?)
                      (let* ([tree (compute-grants)]
                             [root (calculate-root tree)])
                        ;; verify the root
                        (unless (eqv? (msg:token-event-root m) root)
                          (declaim "expected root ~s, got ~s" root (msg:token-event-root m))
                          (halt))
                        ;; looks good
                        (set! grants tree)
                        (handle-data-requests))))
                  (define (handle-data-requests)
                    (handle-message (m das-msg?)
                      (das-msg-case m
                        [(find-grant pk)
                         (let loop ([i 0])
                           (if (>= i (length grants))
                               (reply (grant-not-found))
                               (let ([g (list-ref grants i)])
                                 (if (eq? (grant-pk g) pk)
                                     (reply (grant-found i (grant-amount g)))
                                     (loop (add1 i))))))])
                      (handle-data-requests)))
                  (data-availability-service (self))
                  (declaim "das is ~s" (self))
                  (await-token-event))))
     
            (define (make-wallet-holder name amount)
              (let-values ([(pk sk) (make-keypair)])
                (set! source-chain-wallets
                  (cons (make-source-wallet pk amount)
                    source-chain-wallets))
                (spawn (format "wallet-holder:~a" name)
                  (define (await-token-event)
                    (handle-message (m msg:token-event?)
                      ;; Fetch my merkle path
                      (declaim "das = ~s" (data-availability-service))
                      (send (data-availability-service) (find-grant pk))
                      (await-grant-path)))
                  (define (await-grant-path)
                    (handle-message (m das-reply?)
                      (das-reply-case m
                        [(grant-not-found)
                         (declaim "grant not found")
                         (halt)]
                        [(grant-found path amount)
                         (declaim "grant found at path ~a with amount ~a" path amount)
                         (halt)])))
                  (await-token-event))))

            ;; The token-generating entity
            (define (make-tge)
              (spawn "tge"
                (set-timer! 2000 'token-event)
                (handle-message (m (exactly? 'token-event))
                  (declaim "initiate token event at time ~s" (global-time))
                  (let* ([tree (compute-grants)]
                         [root (calculate-root tree)])
                    (broadcast (make-msg:token-event root))
                    (halt)))))

            (define-datatype settlement-msg
              (batched-grants-root))
        
            ;; ;; The Cardano settlement layer
            ;; (define (cardano)
            ;;   (spawn "cardano"
            ;;     (handle-message (m msg:token-event?)
              
            

            (make-data-availability-service)
            (for-each (lambda (pr)
                        (make-wallet-holder (car pr) (cdr pr)))
              #;`((a . 10) (b . 20) (c . 30) (d . 40) (e . 50) (f . 60) (g . 70) (h . 80) (k . 90))
              `((a . 10) (b . 20) (c . 30)))
            (make-tge)
            )))))
  )
