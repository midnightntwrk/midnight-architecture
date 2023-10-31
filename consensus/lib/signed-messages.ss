;;; ------------------------------------------------------------------------
;;;                                  Copyright 2023, Input Output Hong Kong

(library (consensus lib signed-messages)
  (export
    signed-message make-signed-message signed-message?
    signed-message-m signed-message-sigma
    sign-message verify-signed-message)
  (import
    (chezscheme)
    (consensus lib verify)
    (only (consensus lib common) display-pretty-bytes)
    (only (consensus lib leader-election) lookup-pk)
    (only (scheme-actors yassam) sender)
    (slib openssl crypto)
    (slib utils))


  ;; ---------------------------------------------------------
  ;; Message signing and verifying
  (define-record-type signed-message
    (nongenerative)
    ;; m = message
    ;; sigma = signature (a signed bytevector of the msg contents)
    (fields m sigma)
    (protocol
      (lambda (new)
        (lambda (sk m)
          (let ([bv (message->bytevector m)])
            (new m (sha256-sign (list bv) sk)))))))
  (define sign-message make-signed-message)
  (define (message->bytevector m)
    (let ([tx (make-transcoder (latin-1-codec) (eol-style lf)
                (error-handling-mode replace))])
      (call-with-bytevector-output-port
        (lambda (p) (write m p))
        tx)))
  (define-who verify-signed-message
    (case-lambda
      [(sm pk) (verifying who [bv (message->bytevector (signed-message-m sm))]
                 (and
                   ;; verify sig
                   (verify (sha256-verify (list bv) (signed-message-sigma sm) pk))
                   (signed-message-m sm)))]
      [(sm) (verifying who [pid (sender)]
              (cond
                [(verify (lookup-pk pid)) =>
                 (lambda (pk)
                   (verify-signed-message sm pk))]
                [else #f]))]))

  (record-writer (record-type-descriptor signed-message)
    (lambda (r p wr)
      (display "#signed<" p)
      (wr (signed-message-m r) p)
      (display " " p)
      (display-pretty-bytes (signed-message-sigma r) p)
      (display ">" p)))


  ) ;; library
;;; ------------------------------------------------------------------------
