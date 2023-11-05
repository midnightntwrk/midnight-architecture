;;; ------------------------------------------------------------------------
;;;                                  Copyright 2023, Input Output Hong Kong
;;
(library (simplex-alt1)
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

  (define (bugme label val)
    (bug (format "~a: ~a" (self) label) val))

  (define (?broadcast/me msg)
    (unless (zero? (random 300))
      (broadcast/me msg)))
  
  ;; ------------------------------------------------------------------
  ;; Datatypes

  ;; Traverse an existing chain, returning the number of leading dummy
  ;; blocks and the head of the longest ancestor chain with a
  ;; non-dummy head.
  (define (count-dummies-return-rest chain)
    (let loop ([d 0] [ls chain])
      (cond
        [(dummy-block? (block-ext-block (car ls)))
         (loop (add1 d) (cdr ls))]
        [else (values d ls)])))
  
  ;; This is NOT the block from the simplex paper. Instead:
  ;;
  ;;   **Blocks, block heights, and genesis block.** A *block* $b$ is
  ;;   a tuple $(h, \textsf{parent}, d, \textsf{txs})$, where $h\in
  ;;   \mathbb{N}$ is referred to as the *height* of the block,
  ;;   $\textsf{parent}$ is the hash of a "parent" blockchain, $d\in
  ;;   \mathbb{N}$ is the number of dummy blocks between the parent
  ;;   blockchain and the proposed block, and $\textsf{txs}$ is an
  ;;   arbitrary sequence of strings corresponding to transactions
  ;;   contained in the block. Define the *genesis block* to be the
  ;;   special tuple $b_0 := (0, H(0), 0, \emptyset)$.
  ;;
  (define-record-type block
    (nongenerative)
    (fields h parent-hash d txs)
    (protocol
      (lambda (new)
        (lambda (h parent-chain txs) ;; must specify parent chain, not hash
          (cond
            ;; Genesis block
            [(= h 0) (new 0 (sha256-hash '()) 0 '())]
            ;; Dummy block
            [(bot? parent-chain) (new h bot bot bot)]
            ;; Ordinary block
            [else
              (let-values ([(d chain) (count-dummies-return-rest parent-chain)])
                (new h (hash-blockchain chain) d txs))])))))

  (define (block->bytevector b)
    (let ([tx (make-transcoder (latin-1-codec) (eol-style lf)
                (error-handling-mode replace))])
      (call-with-bytevector-output-port
        (lambda (p)
          (fprintf p "block ~s ~s ~s ~s"
            (block-h b)
            (block-parent-hash b)
            (block-d b)
            (block-txs b)))
        tx)))
  
  (define-who (well-formed-block? b)
    ;; Validation of the parent reference happens in context, using
    ;; `well-formed-blockchain?`.
    (verifying who b
      (and (verify (block? b))
           (verify (nonnegative? (block-h b)))
           (or (dummy-block? b)
               (and
                 (verify (bytevector? (block-parent-hash b)))
                 (verify (nonnegative? (block-d b)))
                 (verifying who [txs (block-txs b)]
                   (or (bot? txs)
                       (and
                         (verify (list? txs))
                         (verify (andmap well-formed-transaction? txs))))))))))

  ;; Convert a bytevector into a number suitable for Chez hashtable keys.
  (define (hash-bytevector bv)
    (mod (u8-bytevector->integer bv) (expt 2 32))
    )

  (define (make-bytevector-hashtable)
    (make-hashtable
      hash-bytevector
      bytevector=?))

  (define-record-type block-ext
    (nongenerative)
    (fields
      block ;; the block for which this is the ext
      votes ;; signatures
      (mutable notarized?)
      finalizers
      (mutable finalized?)
      (mutable unnotarized-ancestors) ;; block-exts
      (mutable beneficiaries) ;; block-exts
      )
    (protocol
      (lambda (new)
        (lambda (block)
          (new block
            (make-bytevector-hashtable)
            (eq? block genesis-block) ;; auto notarized
            (make-bytevector-hashtable)
            (eq? block genesis-block) ;; auto finalized
            '()
            '()
            )))))
  (define (chain-notarized? chain)
    (andmap block-ext-notarized? chain))

  ;; This is an important operation, with side effects, that adds a
  ;; new block-ext to a chain and updates all the mutable pointers
  ;; required to track notarizations.
  (define block-cons
    (case-lambda
      [(h parent-chain d txs)
       (assert (list? parent-chain))
       (block-cons (make-block h txs parent-chain)
         parent-chain)]
      [(block parent-chain)
       (assert (list? parent-chain))
       (let* ([block-ext (cond
                           [(block? block) (make-block-ext block)]
                           [(block-ext? block) block]
                           [else (errorf 'block-cons "not a block ~s" block)])]
              [new-chain (cons block-ext parent-chain)])
         ;; We must scan past any dummies to find the true parent.
         (let-values ([(d definite-chain) (count-dummies-return-rest parent-chain)])
           ;; Extract inductive info about unnotarized-ancestors from
           ;; the 'parent' block, not any dummies in between.  
           (let ([definite-parent (car definite-chain)])
             (block-ext-unnotarized-ancestors-set! block-ext
               (let ([b* (block-ext-unnotarized-ancestors definite-parent)])
                 (if (block-ext-notarized? definite-parent)
                     b*
                     (cons definite-parent b*)))))
           ;; If any leading dummy blocks are unnotarized, add them as
           ;; unnotarized-ancestors.
           (let loop ([i 0] [ls parent-chain])
             (when (< i d)
               (unless (block-ext-notarized? (car ls))
                 (block-ext-unnotarized-ancestors-set! block-ext
                   (cons (car ls)
                     (block-ext-unnotarized-ancestors block-ext))))
               (loop (add1 i) (cdr ls))))
           ;; For every unnotarized ancestor, register the new block
           ;; as a 'beneficiary' so we can remove them from the
           ;; unnotarized-ancestors when they become notarized.
           (for-each
             (lambda (b)
               (unless (block-ext-notarized? b)
                 (block-ext-beneficiaries-set! b
                   (cons block-ext
                     (block-ext-beneficiaries b)))))
             (block-ext-unnotarized-ancestors block-ext)))
         new-chain)]))
             

  ;; Serialize the block's string representation and hash that.
  (define (hash-block b)
    (assert (block? b))
    (sha256-hash (list (block->bytevector b))))
  
  ;; When we hash a block, we hash just the protocol's notion of the
  ;; block, not the full block-ext record.
  (define (hash-block-ext b)
    (assert (block-ext? b))
    (hash-block (block-ext-block b)))

  ;; Blockchain blocks are a descending linked list (b_h, ..., b_0)
  (define (blockchain? x) (and (list? x) (andmap block-ext? x)))

  ;; Optimistically hash a chain assuming the shape (b_h, ..., b_0) by
  ;; hashing together the block hash of b_h with its parent hash.
  ;; This operation relies on just the first element of the list.  To
  ;; verify a well-formed blockchain, call `well-formed-blockchain?`
  (define (hash-blockchain b*)
    (verifying 'hash-blockchain b*
      (verify (andmap block-ext? b*))
      (verify (block? (block-ext-block (car b*)))))
    (cond
      [(null? b*) (sha256-hash '())]
      [(= 1 (length b*))
       (assert (eq? (car b*) genesis-block-ext))
       (hash-block-ext genesis-block-ext)]
      [else (let ([pph (block-parent-hash
                         (block-ext-block (car b*)))])
              (sha256-hash
                (list pph
                  (hash-block
                    (block-ext-block (car b*))))))]))
  
  (define (well-formed-blockchain? b*)
    (verifying 'well-formed-blockchain? b*
      (or
        ;; base case
        (and (null? (cdr b*))
             (verify (eq? (car b*) genesis-block-ext)))
        ;; induction
        (verifying 'block [b (block-ext-block (car b*))]
          (and (verify (block? b))
               (verify (bytevector=?
                         (block-parent-hash b)
                         (hash-blockchain (cdr b*))))
               ;; Gapless sequence of slots at each height h
               (verify (= (block-h b)
                         (add1 (block-h (block-ext-block (cadr b*))))))
               ;; TODO: check leader validity? (we didn't record the proposer's pid)
               (well-formed-blockchain? (cdr b*)))))))

  ;; The paper does not specify transaction content, but we will need
  ;; something for testing. This format stores the pid of a client,
  ;; the timestamp of creation, and a tip amount.
  ;; (define-record-type transaction
  ;;   (nongenerative)
  ;;   (fields pid created tip))
  ;; (define (well-formed-transaction? x)
  ;;   (and (transaction? x)
  ;;        (integer? (transaction-pid x))
  ;;        (nonnegative? (transaction-pid x))
  ;;        (nonnegative? (transaction-tip x))))
  ;; (define (tx<? a b) (< (transaction-tip a) (transaction-tip b)))
  ;; (define (random-transaction n)
  ;;   (make-transaction (self) (global-time) (random n)))

  (define (well-formed-transaction? x) (number? x))

  (define (make-dummy-block h)
    (make-block h bot bot))
  (define (dummy-block? b)
    (bot? (block-parent-hash b)))

  ;; ------------------------------------------------------------------
  (define genesis-block (make-block 0 bot bot))
  (define genesis-block-ext (make-block-ext genesis-block))
  
  ;; ------------------------------------------------------------------
  ;; Signed protocol messages
  (define-datatype Protocol-message
    (Propose b)
    (Vote b)
    (Finalize h)
    )

  ;; Similation control messages
  (define-datatype Control-message
    (Init)
    (Timeout h)
    (Stop)
    )
  
  (define (ht-add! label ht k v)
    (let ([len (vector-length (hashtable-keys ht))])
      (hashtable-set! ht k v)
      (bugme label (format "~a -> ~a on key ~s"
                     len
                     (vector-length (hashtable-keys ht))
                     (if (bytevector? k)
                         (hash-bytevector k)
                         k)))))

  (define emitted-db (make-eqv-hashtable))

  ;; The slot height of a chain
  (define (chain-h chain)
    (block-h (block-ext-block (car chain))))
  
  ;; Return the prefix of a chain up to height h
  (define (chain-prefix chain h)
    (let ([ch (chain-h chain)])
      (if (>= ch h)
          (let loop ([i (- ch h)] [ls chain])
            (if (zero? i)
                ls
                (loop (sub1 i) (cdr ls))))
          chain)))

  ;; Return the block at slot h in the chain, or #f if the
  ;; chain is too short.
  (define (chain-ref chain h)
    (let ([ch (chain-h chain)])
      (and (>= ch h)
           (car (chain-prefix chain h)))))
  
  ;; Return #t if the chain `pre` is a prefix of `chain`.
  ;; This assumes all chains are interned, allowing use
  ;; of eq? to determine constant-time equality.
  (define (chain-prefix? pre chain)
    (eq? pre (chain-prefix chain (chain-h pre))))
  
  (define (node)
    (define $Delta 100)
    (define sk 'uninitialized-sk)
    (define init-chain (list genesis-block-ext))
    (define h 1) ;; 'height' -- the index of the current slot being decided
    (define pending-proposal #f) ;; a proposal for h whose chain is not yet notarized
    (define longest-notarized-chains (list (list genesis-block))) ;; <- may have leading dummies
    (define longest-finalized-chain init-chain) ;; <- may have leading dummies
    (define highest-finalized-slot 0)
    (define timer-fired? #f)
    (define (check-for-pending-proposal!)
      (when (and pending-proposal
                 (= (block-h pending-proposal) h))
        (cond
          [(hashtable-ref chain-db (block-parent-hash pending-proposal) #f) =>
           (lambda (chain)
             (when (chain-notarized? chain)
               (set! pending-proposal #f)
               (do-vote pending-proposal)))])))
    ;; It is possible that both a proposal for h and a dummy block for
    ;; h will both receive a quorum of votes. Finalization will
    ;; eventually decide which is valid. The leader at slot h does not
    ;; wait to see whether both receive a quorum; it simply proposes a
    ;; new chain based on the first quorum it sees. Later evidence may
    ;; show that a different chain was adopted by consensus, meaning both
    ;; that the leader's proposal at h was deemed invalid AND that the
    ;; leader's longest chain is not valid. I.e., we must be able to
    ;; accept multiple longest chains at a given height, act on the first
    ;; one when we are leader, but extend whichever consensus deems the
    ;; winner by a tally of finalizations.
    (define (check-for-longest-chain! chain)
      (let ([chain-height (chain-h chain)])
        (when (chain-notarized? chain)
          (if (= chain-height (- h 1))
              ;; Then we have a new rival longest chain at height h-1.
              (begin 'ignore
                     (set! longest-notarized-chains
                       (cons chain longest-notarized-chains))
                )
              ;; Else, check for the first longest chain at height h.
              (when (>= chain-height h)
                ;; The first time we see a chain notarized at some new h, we
                ;; advance to h + 1.  If we properly check-for-longest-chain!
                ;; after every notarization, it should be the case that the
                ;; new chain height is exactly h.  If it isn't, we have other
                ;; bookkeeping to mangage, like voting to finalize intermediate
                ;; blocks.  Best if we avoid that.
                (verifying 'check-for-longest-chain! h
                  (assert (verify (= chain-height h))))
              
                ;; Make sure the chain is consistent with the finalized prefix.
                (verifying 'viable-notarized chain
                  (assert (verify (chain-prefix? longest-finalized-chain chain))))
              
                ;; The protocol requires we broadcast a Finalize
                ;; message unless our timer fired for slot h causing us to
                ;; vote for the dummy block at h.
                ;;
                ;; “an honest player only votes for either ⟨finalize, h⟩, or
                ;; ⟨vote, h, ⊥h⟩, and never both” ([Chan and Pass, 2023,
                ;; p. 11])
                ;;
                (unless timer-fired?
                  (?broadcast/me
                    (sign-message sk
                      (Finalize h))))
              
                ;; Now we can update to the new h
                (set! longest-notarized-chains (list chain))
                (set! h (add1 h))
                (set! pending-proposal #f)
                (declaim "h = ~a" h)
              
                ;; If leader, propose.
                (when (leader? (self) h)
                  (if (zero? (random 3))
                      (bugme 'suppressed-propose h)
                      (do-propose! h chain)))
              
                ;; Finally, set a timer for this slot.
                (set-timer! (* $Delta 3) (Timeout h))
                (set! timer-fired? #f)
                )))))
    (define emit-finalized!
      (let ([txs (lambda (b)
                   (block-txs
                     (block-ext-block b)))])
        (lambda (newly-final)
          (let ([cell (hashtable-cell emitted-db (self) '())])
            (set-cdr! cell
              (append  (map txs newly-final)
                (cdr cell)))))))
    (define orphaned-blocks '())
    ;; The block-ext-db encodes orphans as single-element chains.
    (define block-ext-db (make-bytevector-hashtable)) ;; -> chain
    (define dummy-block-ext-db (make-bytevector-hashtable)) ;; -> block-ext
    (define (orphan? chain)
      (and (null? (cdr chain))
           (not (eq? (car chain) genesis-block-ext)))) ;; block-hash -> (block-ext, ..., genesis)
    (define (un-orphan! block-ext chain)
      (assert (list? chain))
      (set! orphaned-blocks (remq block-ext orphaned-blocks))
      (let ([chain (block-cons block-ext chain)])
        (hashtable-set! block-ext-db (hash-block-ext block-ext) chain)
        (check-for-pending-proposal!)
        (check-for-longest-chain! chain)))
    (define chain-db (make-bytevector-hashtable)) ;; chain-hash -> chain
    (define do-propose!
      (let ([highest-proposed 0])
        (lambda (h parent-chain)
          (declaim "pid ~a proposing at slot ~a" (self) h)
          (verify (well-formed-blockchain? parent-chain))
          (when (> h highest-proposed)
            (set! highest-proposed h)
            (?broadcast/me
              (sign-message sk
                (Propose
                  (if #f ;; (zero? (random 20))
                      ;; create 25% bogus blocks
                      (make-block h parent-chain (list 'bogus))
                      ;; create 75% good blocks
                      (make-block h parent-chain (list (+ (self) (global-time))))))))))))
    (define (do-vote-dummy! h)
      (bugme 'do-vote-dummy! h)
      (declaim "h = ~a, vote dummy" h)
      (?broadcast/me
        (sign-message sk
          (Vote (make-dummy-block h)))))
    (define (do-vote b)
      (declaim "h = ~a, vote ~s" h b)
      (?broadcast/me
        (sign-message sk
          (Vote b))))
    (define (add-vote! block-ext sig)
      (unless (block-ext-notarized? block-ext)
        (let ([votes (block-ext-votes block-ext)])
          (hashtable-set! votes sig #t) ;; <- add sig to hash set
          (bugme 'add-vote! (format "pid ~a, sig ~a signed vote for ~a"
                              (sender) (mod (u8-bytevector->integer sig) 1000000) block-ext))
          (bugme 'add-vote! (format "~a votes for ~a"
                              (vector-length (hashtable-keys votes))
                              block-ext))
          (when (quorum? (vector-length (hashtable-keys votes)))
            (bugme 'add-vote! (format "vote quorum at height ~a for ~s"
                                (block-h (block-ext-block block-ext))
                                block-ext))
            (if (dummy-block? (block-ext-block block-ext))
                (bugme 'add-vote! (format "notarized dummy block at h=~a"
                                    (block-h (block-ext-block block-ext))))
                (bugme 'add-vote! (format "notarized full block at h=~a with d=~a"
                                    (block-h (block-ext-block block-ext))
                                    (block-d (block-ext-block block-ext)))))
            (block-ext-notarized?-set! block-ext #t)))))
    ;; Possible issue: This function will silently drop a finalize vote
    ;; for a block it cannot find in all its longest notarized chains.
    ;; Is this expected behavior, or should we be remembering this vote
    ;; somewhere else?
    (define (add-finalizer! h sig)
      (let ([block-exts (map (lambda (c) (chain-ref c h)) longest-notarized-chains)])
        (unless (null? block-exts)
          (let ([block-ext (car block-exts)])
            (when (and block-ext ;; <- #f if chain too short
                       (> h highest-finalized-slot)
                       (verify (andmap (lambda (x) (eq? x block-ext)) (cdr block-exts)))
                       (verify (block-ext? block-ext)))
              (unless (block-ext-finalized? block-ext)
                (let ([finalizers (block-ext-finalizers block-ext)])
                  (hashtable-set! finalizers sig #t) ;; <- add sig to hash set
                  #;(bugme 'add-finalizer! (format "~a signed finalizer for ~a"
                                           (mod (u8-bytevector->integer sig) 1000000) block-ext))
                  #;(bugme 'add-finalizer! (format "~a finalizers for ~a"
                                           (vector-length (hashtable-keys finalizers))
                                           block-ext))
                  (when (quorum? (vector-length (hashtable-keys finalizers)))
                    #;(bugme 'add-finalizer! (format "finalizer quorum at height ~a for ~s"
                                             (block-h (block-ext-block block-ext))
                                             block-ext))
                    (block-ext-finalized?-set! block-ext #t)
                    (let ([prev-highest highest-finalized-slot]
                          [prev-chain longest-finalized-chain])
                      (set! highest-finalized-slot h)
                      ;; pin the longest finalized chain
                      (cond
                        [(hashtable-ref block-ext-db (hash-block-ext block-ext) #f) =>
                         (lambda (chain)
                           (set! longest-finalized-chain chain)
                           (emit-finalized!
                             (let loop ([acc '()] [chain chain])
                               (if (eq? chain prev-chain)
                                   acc
                                   (loop (cons (car chain) acc) (cdr chain))))))]
                        [else (bugme 'add-finalizer! (format "not found: ~s" block-ext))]))))))))))
    (define highest-proposal-per-process (make-eqv-hashtable))
    (define (get-highest-proposal p)
      (cond
        [(hashtable-ref highest-proposal-per-process p #f) => identity]
        [else
          (hashtable-set! highest-proposal-per-process p 0)
          0]))
    (define (quorum? n)
      (>= n (/ (* 2 (length (cohort))) 3.0)))
    (define (find/create-dummy-blocks h d chain)
      (let loop ([h h] [d d])
        (cond
          [(zero? d) chain]
          ;; Important: the following is cons, not block-cons.  We
          ;; don't know for certain the parent of a dummy block at
          ;; this point, so we don't wire-up its notarization fwd/back
          ;; links with the proposed ancestor chain.  The beauty is
          ;; that we never need to do so; we will never ask whether
          ;; a block with a dummy head is notarized, so we don't need
          ;; to ensure recursive notarization.
          [else (cons (intern-dummy-block (make-dummy-block h))
                  (loop (- h 1) (- d 1)))])))
    ;; Interning a dummy block is a simple matter of find-or-create,
    ;; where creation does not include any "wiring up" because it has
    ;; no parent chain to wire into.
    (define (intern-dummy-block block) ;; block -> block-ext
      (assert (dummy-block? block))
      (cond
        [(hashtable-ref dummy-block-ext-db (hash-block block) #f) =>
         (lambda (x) x)]
        [else
          (let ([block-ext (make-block-ext block)])
            (hashtable-set! dummy-block-ext-db (hash-block block) block-ext)
            block-ext)]))
    (define (intern-block block) ;; block -> chain
      (assert (and (block? block) (not (dummy-block? block))))
      (unless (zero? (block-d block))
        (bugme "intern with dummy prefix" block))
      (cond
        [(hashtable-ref block-ext-db (hash-block block) #f) =>
         (lambda (x) x)]
        [else
          (let ([block-ext (make-block-ext block)])
            (cond
              [(hashtable-ref chain-db (block-parent-hash block) #f) =>
               (lambda (ls)
                 (assert (list? ls))
                 ;; This is the crux of our alt protocol, where we
                 ;; synthesize a chain by (a) locating the referenced
                 ;; parent chain and (b) finding or synthesizing all
                 ;; the dummy blocks between the parent and the new
                 ;; block.
                 (let* ([chain
                          (block-cons block ;; <- block-cons does internal wiring
                            (find/create-dummy-blocks
                              (- (block-h block) 1)
                              (block-d block)
                              ls))]
                        [chain-hash (hash-blockchain chain)])
                   (verifying 'block-cons chain
                     (assert (verify (well-formed-blockchain? chain))))
                   (hashtable-set! block-ext-db (hash-block block) chain)
                   (hashtable-set! chain-db chain-hash chain)
                   ;; Check whether this new chain un-orphans any blocks.
                   (for-each
                     (lambda (b)
                       (when (bytevector=? (block-parent-hash (block-ext-block b)) chain-hash)
                         (un-orphan! b chain)))
                     orphaned-blocks)
                   ;; return the chain
                   chain))]
              ;; Parent not yet interned.  Remember this as an orphan block.
              [else
                (let ([chain (list block-ext)])
                  (hashtable-set! block-ext-db (hash-block block) chain)
                  (set! orphaned-blocks (cons block-ext orphaned-blocks))
                  chain)]))]))
    (spawn "p"
      (let* ([keys (create-key-pair)]
             [_sk (car keys)]
             [pk (cdr keys)])
        (set! sk _sk)
        (cohort (cons (cons (self) pk) (cohort))))
      (hashtable-set! chain-db (hash-blockchain init-chain) init-chain)
      (let always ()
        (handle-message (m any?)
          ;; (bugme 'received m)
          (cond
            [(Control-message? m)
             (Control-message-case m
               [(Init)
                (when (and (= h 1) (leader? (self) 1))
                  (declaim "pid ~a is the initial leader at slot ~a" (self) 1)
                  (do-propose! 1 init-chain))
                (always)]
               [(Timeout slot-h)
                (when (= slot-h h)
                  (bugme 'Timeout h)
                  (declaim "h = ~a; Timeout" h)
                  (set! timer-fired? #t)
                  (do-vote-dummy! h))
                (always)]
               [(Stop) (halt)])]
            [(signed-message? m)
             (let ([vm (verify-signed-message m)])
               (when (Protocol-message? vm)
                 (Protocol-message-case vm
                   ;; --------------------------------------------
                   [(Propose b)
                    ;; (bugme 'proposal `(,(sender) ,b))
                    (when (and (not (dummy-block? b))
                               (well-formed-block? b))
                      ;; It's an incredibly subtle point about Simplex that a
                      ;; process may vote for both a proposal at h and a dummy
                      ;; block at h.  The tie break is the Finalize votes
                      ;; because a process that voted for a dummy block cannot
                      ;; also vote to finalize the slot. When the timer fires
                      ;; and we vote for a dummy block, it's the normal case
                      ;; that we voted for the proposal at h already.  The timer
                      ;; isn't waiting for a proposal, it's waiting for
                      ;; notarization of something at h.
                      (when (and (= (block-h b) h)
                                 (leader? (sender) (block-h b))
                                 (> (block-h b) (get-highest-proposal (sender))))
                        (cond
                          ;; An important question here is how much extra notarization data
                          ;; we include in a proposal.  The paper includes the proposer's
                          ;; entire notarization evidence for the chain.  We can safely
                          ;; omit notarization data for blocks below the highest finalized
                          ;; (inclusive), but what about those above?  If we omit them, we
                          ;; might fail to vote for a valid proposal just because we were
                          ;; not yet caught up.  This creates unnecessary dummy blocks and
                          ;; lowered throughput.  So we might instad include the leader's
                          ;; notarizations for all non-finalized blocks. Or we might store
                          ;; the proposal and defer our vote.
                          [(hashtable-ref chain-db (block-parent-hash b) #f) =>
                           (lambda (chain)
                             (if (chain-notarized? chain)
                                 (do-vote b)
                                 (set! pending-proposal b)))]
                          [else (set! pending-proposal b)])))]
                   ;; --------------------------------------------
                   [(Vote b)
                    ;; (bugme 'vote `(,(sender) ,b))
                    (when (well-formed-block? b)
                      (let-values ([(chain block-ext)
                                    (if (dummy-block? b)
                                        (values '(not-a-chain) (intern-dummy-block b))
                                        (let* ([chain (intern-block b)]
                                               [block-ext (car chain)])
                                          (values chain block-ext)))])
                        (unless (block-ext-notarized? block-ext)
                          (add-vote! block-ext (signed-message-sigma m))
                          (when (block-ext-notarized? block-ext) ;; edge detect
                            ;; Bookkeeping
                            (for-each
                              (lambda (b)
                                (block-ext-unnotarized-ancestors-set! b
                                  (remv block-ext
                                    (block-ext-unnotarized-ancestors b))))
                              (block-ext-beneficiaries block-ext))
                            ;; Maybe vote for a pending proposal
                            (check-for-pending-proposal!)
                            ;; Maybe update longest chain
                            (check-for-longest-chain! chain)))))]
                   ;; --------------------------------------------
                   [(Finalize h)
                    (add-finalizer! h (signed-message-sigma m))]
                   )))
             (always)]
            [else (always)])))))
  
  
  ;; ------------------------------------------------------------------
  (define (run-tests)
    #;(parameterize ([cohort '(a b c d)])
      (verifying 'leader-election [l (leader 3)]
        (and
          (verify (symbol? l))
          (verify (member l (cohort))))))
    #;(let ()
      (define null-chain (list genesis-block-ext))
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
    (call-with-output-file "simplex.puml"
      (lambda (p)
        (with-event-processor (write-plantUML p)
          (with-scheduler (event-handler (lambda (x) x))
            (node) (node) (node) ;; (node) (node)
            (spawn "starter"
              (set-timer! 200 'init)
              (handle-message (m (exactly? 'init))
                (broadcast (Init))
                (halt)))
            (spawn "stopper"
              (set-timer! 50000 'stop)
              (handle-message (m (exactly? 'stop))
                (broadcast (Stop))
                (halt)))
            (spawn "observer"
              (let loop ()
                (handle-message (m any?)
                  (cond
                    [(equal? m (Stop)) (set-timer! 300 'report) (loop)]
                    [(eq? m 'report)
                     (printf "final report\n")
                     (let-values ([(keys vals) (hashtable-entries emitted-db)])
                       (vector-for-each
                         (lambda (k v)
                           (printf "<<~a>>" k)
                           (for-each
                             (lambda (sublist)
                               (for-each
                                 (lambda (tx)
                                   (display " ")
                                   (write tx))
                                 sublist))
                             (reverse v))
                           (newline))
                         keys vals)
                       (newline))
                     (halt)]
                    [else (loop)]))))
            )))
      'truncate)
    #t)
  

  ;; ------------------------------------------------------------------

  (record-writer (type-descriptor block)
    (lambda (r p wr)
      (display "#block<" p)
      (wr (block-h r) p)
      (display " " p)
      (if (bytevector? (block-parent-hash r))
          (display-pretty-bytes (block-parent-hash r) p)
          (display (block-parent-hash r) p))
      (display " " p)
      (wr (block-d r) p)
      (display " " p)
      (wr (block-txs r) p)
      (display ">" p)
      ))

  (record-writer (type-descriptor block-ext)
    (lambda (r p wr)
      (display "#block-ext<" p)
      (wr (block-ext-block r) p)
      (display ">" p)))
  
  
  ) ;; library
;;; ------------------------------------------------------------------------

