;;; ------------------------------------------------------------------------
;;;                                  Copyright 2023, Input Output Hong Kong
;;; ------------------------------------------------------------------------

(library (glacier-drop)
  (export run-tests)
  (import
    (chezscheme)
    (scheme-actors yassam)
    (slib openssl crypto)
    ;;(slib faux-ppk)
    (slib datatype)
    )

  (define (bug label val)
    (printf "BUG  ~a => ~s\n" label val)
    val)
    
  (define-record-type public-key (nongenerative) (fields bv))
  (define-record-type secret-key (nongenerative) (fields bv))
;;  (define-record-type hashval (nongenerative) (fields bv))
  
  (define (exactly? x) (lambda (y) (equal? y x)))

  (define (not-implemented) (errorf 'not-implemented ""))
  
  (define (run-tests)
    (call-with-output-file "glacier-drop.puml"
      (lambda (p)
        (with-event-processor (write-plantUML p)
          (with-scheduler (event-handler (trace-lambda handler (x) x))

            (define-record-type source-wallet (nongenerative) (fields pk amount))
            (define-record-type grant (nongenerative) (fields pk amount))
            (define-record-type msg:token-event (nongenerative) (fields root))
            (define-record-type msg:award-claim (nongenerative) (fields pk))
            ;; Messages to/from the Data Availability Service (das)
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
              (let* ([pr (create-key-pair)]
                     [sk (make-secret-key (car pr))]
                     [pk (make-public-key (cdr pr))])
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

            #|

            The token-event has a first phase where it publishes the merkle root
            and collects verification votes from volunteers.  Each volunteer
            confirms the root and includes a unique path to their grant with an
            unlocking proof for a wallet of "sufficient" size.  When the tge
            contract receives enough of these, it enters the "claiming" phase.

            The voters have proven some key things to us:
            - Interest
            - Responsiveness
            - Sufficient stake to lower the risk of Sybil attack

            These are the candidate pool to operate the first Hydra head.
            If we have 100 in the pool, we just need a random 10 for
            the head.

            At this point we go into a loop of:
            - Selecting a random committee
            - Trying to form a Hydra head
            - Operating the Hydra head to collect and verify claims
               - model the Hydra voting protocol
               - maintain claim tree state on the das
            - Closing the Hydra head to checkpoint the Merkle root of the claim tree

            NB: There is an off-by-one error on the final cohort.  They need to
            be given their awards without serving as a committee.

            |#

            (define-record-type msg:contract-control
              (nongenerative)
              (fields signed-nonce msg))
            (define-datatype contract-control
              (deploy merkle-root))

            ;; The contract-transition messages represent observable
            ;; changes in the contract state.  They are represented
            ;; as broadcasts of the event and state, but in reality
            ;; would just be state updates on chain.
            (define-datatype contract-transition
              (deployed merkle-root)
              )

            (define (glacier-drop-contract pk quorum-size min-voter-stake)
              (spawn "contract"
                (define (collect-initial-verifications claims)
                  (if (= (length claims) quorum-size)
                      (begin
                        ;; compute initial claims-tree and merkle root
                        (not-implemented)
                        ;; broadcast them
                        (not-implemented)
                        ;; start trying to create Hydra batches
                        (try-create-hydra-head
                          (map msg:award-claim-pk claims)))
                      (handle-message (m msg:award-claim?)
                        ;; verify the path, ownership, and the amount
                        (not-implemented)
                        ;; check for double claim
                        (not-implemented)
                        ;; add to claims
                        (collect-initial-verifications (cons m claims)))))
                (define (try-create-hydra-head claims)
                  (not-implemented))
                ;; -------------------------------------
                ;; Wait for 'deploy' message
                (handle-message (m msg:contract-control?)
                  (contract-control-case m
                    [(deploy merkle-root)
                     ;; Broadcast the initial call for verification
                     (broadcast (deployed merkle-root))
                     (collect-initial-verifications '())]))))
                  

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
            )))
      'truncate))

  (define (bv->s bv)
    (let ([tx (make-transcoder (utf-8-codec) (eol-style lf)
                (error-handling-mode replace))])
      (bytevector->string bv tx)))
  
  (record-writer (type-descriptor public-key)
    (lambda (r p wr)
      (let* ([str (bv->s (public-key-bv r))]
             [len (string-length str)])      
        (display "#pk<..." p)
        (display (substring str (- len (+ 127 16)) (- len 127)) p)
        (display "...>" p)
      )))

  (record-writer (type-descriptor secret-key)
    (lambda (r p wr)
      (let* ([str (bv->s (secret-key-bv r))]
             [len (string-length str)])      
        (display "#sk<..." p)
        (display (substring str (- len (+ 127 16)) (- len 127)) p)
        (display "...>" p)
      )))
  
  )
