;;; ------------------------------------------------------------------------
;;;                                  Copyright 2023, Input Output Hong Kong
;;; ------------------------------------------------------------------------

;; https://medium.com/@StricaHQ/introducing-warp-transactions-689d3e1339c7
;; https://aiken-lang.org/

(library (glacier-drop)
  (export run-tests)
  (import
    (chezscheme)
    (scheme-actors yassam)
    (slib openssl crypto)
    (rename (slib merkle)
      [merkle-proof compute-merkle-proof])
    (slib datatype))

  ;; ---------------------------------------------------------
  ;; We wrap some data types to control printing
  (define-record-type public-key (nongenerative) (fields bv))
  (define-record-type secret-key (nongenerative) (fields bv))
  ;;  (define-record-type hashval (nongenerative) (fields bv))
  (define-record-type merkle-proof (nongenerative) (fields code))
  
  ;; ---------------------------------------------------------
  ;; Utilities
  (define (exactly? x) (lambda (y) (equal? y x)))
  (define (not-implemented) (errorf 'not-implemented ""))
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

  ;; ---------------------------------------------------------
  ;; Data structures for state and messages
  (define-record-type source-wallet (nongenerative) (fields pk amount))
  (define-record-type grant (nongenerative) (fields pk amount))
  
  ;; ---------------------------------------------------------
  ;; Message types
  (define-record-type msg:token-event (nongenerative) (fields root))
  (define-record-type msg:award-claim (nongenerative) (fields pk))

  ;; Messages to/from the Data Availability Service (das)
  (define-datatype Das-request
    (find-grant pk))
  (define-datatype Das-reply
    (grant-not-found)
    (grant-found path amount))
  (define-record-type signed-contract-control
    (nongenerative)
    (fields signed-nonce msg))
  (define-datatype contract-control
    (contract-init merkle-root))
  
  ;; The contract-transition messages represent observable
  ;; changes in the contract state.  They are represented
  ;; as broadcasts of the event and state, but in reality
  ;; would just be state updates on chain.
  (define-datatype contract-transition
    (contract-inited merkle-root)
    )

  (define-datatype settlement-msg
    (batched-grants-root))
        

  
  ;; ---------------------------------------------------------
  ;; Protocol and test suite
  (define (run-tests)
    (call-with-output-file "glacier-drop.puml"
      (lambda (p)
        (with-event-processor (write-plantUML p)
          (with-scheduler (event-handler (trace-lambda handler (x) x))
            ;; A mockup of the source chain (e.g., Cardano) and its
            ;; active wallets.  For our simulation, we let each wallet
            ;; actor post its balance here as it spawns.
            (define source-chain-wallets '())

            ;; There must exist a deterministic function that, given a
            ;; source chain and a reference block for that chain,
            ;; computes the Glacier Drop grants for all the wallets
            ;; live at that block.  There will actually be a different
            ;; such function for each source chain, and a single
            ;; master function that invokes them all and builds the
            ;; aggregate grant database.

            ;; Compute the Merkle leaf for a given pk
            (define (compute-grant pk)
              (let ([w (find (lambda (w) (eqv? (source-wallet-pk w) pk))
                         source-chain-wallets)])
                (and w
                     (make-grant pk
                       (* 10 (source-wallet-amount w))))))
            
            ;; Compute the full Merkle tree
            (define (compute-grants)
              (compute-merkle-tree
                (map
                  (lambda (w)
                    (compute-grant (source-wallet-pk w)))
                  source-chain-wallets)))

            (define (calculate-root tree)
              (merkle-hash tree))

            ;; We assume the existence of a data-availability service.
            ;; We model this as a single actor, but we assume it is
            ;; something more robust and decentralized, like an IPFS
            ;; service.  When we spawn the actor, it registers its pid
            ;; here for easy lookup.
            (define data-availability-service (make-parameter #f))

            ;; The actor implementation of data-availability-service.
            ;;
            ;; While we could model this service as a pure key/value
            ;; store, a more realistic implementation will avoid
            ;; serving the full 1TB image to every client.  Instead,
            ;; we imagine a service that understands the specific
            ;; Merkle tree and can serve Merkle proofs for specific
            ;; wallet data.
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
                    (handle-message (m Das-request?)
                      (Das-request-case m
                        [(find-grant pk)
                         (let ([g (compute-grant pk)])
                           (let ([proof
                                   (and g
                                        (make-merkle-proof
                                          (compute-merkle-proof grants g)))])
                             (if proof
                                 (reply (grant-found proof (grant-amount g)))
                                 (reply (grant-not-found)))))])
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
                    (handle-message (m Das-reply?)
                      (Das-reply-case m
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


            ;; The contract on Cardano.  We represent this as simple
            ;; evolving state machine.
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
                ;; Wait for 'contract-init' message
                (handle-message (m signed-contract-control?)
                  ;; verify signed nonce
                  (not-implemented)
                  (contract-control-case (signed-contract-control-msg m)
                    [(contract-init merkle-root)
                     ;; Broadcast the initial call for verification
                     (broadcast (contract-inited merkle-root))
                     (collect-initial-verifications '())]))))
                  

            ;; The token-generating entity.  This actor initiates the
            ;; token drop and then essentially burns its keys, ensuring
            ;; fullly decentralized launch.
            (define (make-tge)
              (spawn "tge"
                ;; Do nothing for a little while, making sure all
                ;; the wallet holders get a turn to register their
                ;; wallets in the source-chain-wallets DB.
                (set-timer! 2000 'token-event)
                ;; When the timer fires, compute the Merkle tree of
                ;; the grants DB, register the root in the
                ;; glacier-drop contract, and store the tree at the
                ;; data-availability-service.
                (handle-message (m (exactly? 'token-event))
                  (declaim "initiate token event at time ~s" (global-time))
                  (let* ([tree (compute-grants)]
                         [root (calculate-root tree)])
                    (broadcast (make-msg:token-event root))
                    (halt)))))

  

            (make-data-availability-service)
            (for-each (lambda (pr)
                        (make-wallet-holder (car pr) (cdr pr)))
              #;`((a . 10) (b . 20) (c . 30) (d . 40) (e . 50) (f . 60) (g . 70) (h . 80) (k . 90))
              `((a . 10) (b . 20) (c . 30)))
            (make-tge)
            )))
      'truncate))

  ;; ------------------------------------------------------------------
  ;; Pretty printing
  ;;
  ;; NB: record-writer updates are expressions, and must therefore
  ;; be listed after all definitions in the library.
  
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

  (record-writer (type-descriptor merkle-proof)
    (lambda (r p wr)
      (display "#<proof " p)
      (let ([proof-length
              (occurences 'compute-hash
                (flatten (merkle-proof-code r)))])
        (let loop ([i 0])
          (when (< i proof-length)
            (display "🔗" p)
            (loop (add1 i)))))
      (display ">" p)))
  
  )

