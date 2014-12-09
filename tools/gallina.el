;; gallina.el --- Coq mode editing commands for Emacs
;;
;; Jean-Christophe Filliatre, march 1995
;; Shamelessly copied from caml.el, Xavier Leroy, july 1993.
;;
;; modified by Marco Maggesi <maggesi@math.unifi.it> for gallina-inferior

; compatibility code for proofgeneral files
(require 'coq-font-lock)
; ProofGeneral files. remember to remove coq version tests in
; gallina-syntax.el
(require 'gallina-syntax)

(defvar coq-mode-map nil
  "Keymap used in Coq mode.")
(if coq-mode-map
    ()
  (setq coq-mode-map (make-sparse-keymap))
  (define-key coq-mode-map "\t"      'coq-indent-command)
  (define-key coq-mode-map "\M-\t"   'coq-unindent-command)
  (define-key coq-mode-map "\C-c\C-c"   'compile)
)

(defvar coq-mode-syntax-table nil
  "Syntax table in use in Coq mode buffers.")
(if coq-mode-syntax-table
    ()
  (setq coq-mode-syntax-table (make-syntax-table))
  ; ( is first character of comment start
  (modify-syntax-entry ?\( "()1" coq-mode-syntax-table)
  ; * is second character of comment start,
  ; and first character of comment end
  (modify-syntax-entry ?*  ". 23" coq-mode-syntax-table)
  ; ) is last character of comment end
  (modify-syntax-entry ?\) ")(4" coq-mode-syntax-table)
  ; quote is a string-like delimiter (for character literals)
  (modify-syntax-entry ?' "\"" coq-mode-syntax-table)
  ; quote is part of words
  (modify-syntax-entry ?' "w" coq-mode-syntax-table)
)

(defvar coq-mode-indentation 2
  "*Indentation for each extra tab in Coq mode.")

(defun coq-mode-variables ()
  (set-syntax-table coq-mode-syntax-table)
  (make-local-variable 'paragraph-start)
  (setq paragraph-start (concat "^$\\|" page-delimiter))
  (make-local-variable 'paragraph-separate)
  (setq paragraph-separate paragraph-start)
  (make-local-variable 'paragraph-ignore-fill-prefix)
  (setq paragraph-ignore-fill-prefix t)
  (make-local-variable 'require-final-newline)
  (setq require-final-newline t)
  (make-local-variable 'comment-start)
  (setq comment-start "(* ")
  (make-local-variable 'comment-end)
  (setq comment-end " *)")
  (make-local-variable 'comment-column)
  (setq comment-column 40)
  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip "(\\*+ *")
  (make-local-variable 'parse-sexp-ignore-comments)
  (setq parse-sexp-ignore-comments nil)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'coq-indent-command)
  (make-local-variable 'font-lock-keywords)
  (setq font-lock-defaults '(coq-font-lock-keywords-1)))

;;; The major mode

(defun coq-mode ()
  "Major mode for editing Coq code.
Tab at the beginning of a line indents this line like the line above.
Extra tabs increase the indentation level.
\\{coq-mode-map}
The variable coq-mode-indentation indicates how many spaces are
inserted for each indentation level."
  (interactive)
  (kill-all-local-variables)
  (setq major-mode 'coq-mode)
  (setq mode-name "coq")
  (use-local-map coq-mode-map)
  (coq-mode-variables)
  (run-hooks 'coq-mode-hook))

;;; Indentation stuff

(defun coq-in-indentation ()
  "Tests whether all characters between beginning of line and point
are blanks."
  (save-excursion
    (skip-chars-backward " \t")
    (bolp)))

(defun coq-indent-command ()
  "Indent the current line in Coq mode.
When the point is at the beginning of an empty line, indent this line like
the line above.
When the point is at the beginning of an indented line
\(i.e. all characters between beginning of line and point are blanks\),
increase the indentation by one level.
The indentation size is given by the variable coq-mode-indentation.
In all other cases, insert a tabulation (using insert-tab)."
  (interactive)
  (let* ((begline
          (save-excursion
            (beginning-of-line)
            (point)))
         (current-offset
          (- (point) begline))
         (previous-indentation
          (save-excursion
            (if (eq (forward-line -1) 0) (current-indentation) 0))))
    (cond ((and (bolp)
                (looking-at "[ \t]*$")
                (> previous-indentation 0))
           (indent-to previous-indentation))
          ((coq-in-indentation)
           (indent-to (+ current-offset coq-mode-indentation)))
          (t
           (insert-tab)))))

(defun coq-unindent-command ()
  "Decrease indentation by one level in Coq mode.
Works only if the point is at the beginning of an indented line
\(i.e. all characters between beginning of line and point are blanks\).
Does nothing otherwise."
  (interactive)
  (let* ((begline
          (save-excursion
            (beginning-of-line)
            (point)))
         (current-offset
          (- (point) begline)))
    (if (and (>= current-offset coq-mode-indentation)
             (coq-in-indentation))
        (backward-delete-char-untabify coq-mode-indentation))))

;;; gallina.el ends here

(provide 'gallina)
