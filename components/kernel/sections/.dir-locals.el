((nil . ((eval . (message "Loaded formatting.el"))
         (eval . (if (string=
                      "90a8b75056172d4fe184b1061fedf6083cc7e8698be557293b6654fb9039c268"
                      (with-temp-buffer
                        (insert-file-contents "../formatting.el")
                        (secure-hash 'sha256 (current-buffer))))
                     (load-file "../formatting.el"))
                  )
         )
      )
 (latex-mode
  (TeX-master . "../kernel-spec.tex"))
 )
