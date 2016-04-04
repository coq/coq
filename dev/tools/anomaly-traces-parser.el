;; This Elisp snippet adds a regexp parser for the format of Anomaly
;; backtraces (coqc -bt ...), to the error parser of the Compilation
;; mode (C-c C-c: "Compile command: ..."). Once the
;; coq-change-error-alist-for-backtraces function has run, file
;; locations in traces are recognized and can be jumped from easily
;; from the *compilation* buffer.

;; You can just copy everything below to your .emacs and this will be
;; enabled from any compilation command launched from an OCaml file.

(defun coq-change-error-alist-for-backtraces ()
  "Hook to change the compilation-error-regexp-alist variable, to
   search the coq backtraces for error locations"
  (interactive)
  (add-to-list
   'compilation-error-regexp-alist-alist
   '(coq-backtrace
     "^ *\\(?:raise\\|frame\\) @ file \\(\"?\\)\\([^,\" \n\t<>]+\\)\\1,\
      lines? \\([0-9]+\\)-?\\([0-9]+\\)?\\(?:$\\|,\
      \\(?: characters? \\([0-9]+\\)-?\\([0-9]+\\)?:?\\)?\\)"
     2 (3 . 4) (5 . 6)))
  (add-to-list 'compilation-error-regexp-alist 'coq-backtrace))

;; this Anomaly parser should be available when one is hacking
;; on the *OCaml* code of Coq (adding bugs), so we enable it
;; through the OCaml mode hooks.
(add-hook 'caml-mode-hook 'coq-change-error-alist-for-backtraces)
(add-hook 'tuareg-mode-hook 'coq-change-error-alist-for-backtraces)
