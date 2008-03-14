;; coq.el --- Coq mode editing commands for Emacs
;;
;; Jean-Christophe Filliatre, march 1995
;; Honteusement pompé de caml.el, Xavier Leroy, july 1993.
;;
;; modified by Marco Maggesi <maggesi@math.unifi.it> for coq-inferior

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
  (setq indent-line-function 'coq-indent-command))

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

;;; Hilight

(cond 
 (window-system
  (setq hilit-mode-enable-list  '(not text-mode)
        hilit-inhibit-hooks     nil
        hilit-inhibit-rebinding nil)
  
  (require 'hilit19)
       (setq  hilit-quietly t)
       (hilit-set-mode-patterns
        'coq-mode
        '(;;comments
          ("(\\*" "\\*)" comment)
          ;;strings
          (hilit-string-find ?' string)
	  ;;directives
          ("^[ \t]*\\(AddPath\\|DelPath\\|Add[ \t]+ML[ \t]+Path\\|Declare[ \t]+ML[ \t]+Module\\|Require\\|Export\\|Module\\|Opaque\\|Transparent\\|Section\\|Chapter\\|End\\|Load\\|Print\\|Show\\)[ \t]+[^.]*" nil include)
	  ("Implicit[ \t]+Arguments[ \t]+\\(On\\|Off\\)[^.]*" nil include)
          ;;grammar definitions
	  ("^[ \t]*Syntax[ \t]+\\(tactic\\|command\\)" nil define)
	  ("^[ \t]*Syntax[ \t]+\\(tactic\\|command\\)[ \t]*level[ \t]+[0-9]+[ \t]*" nil define)
	  ("^[ \t]*level[ \t]+[0-9]+[ \t]*:" nil define)
	  ("^[ \t]*Grammar.*" ":=" define)
          ("^[ \t]*Tactic[ \t]+Definition" ":=" define) 
	  ("^[ \t]*Token[^.]*" nil define)
	  ("^[ \t]*\\(Coercion\\|Class\\|Infix\\)[ \t]+[[A-Za-z0-9$_\\']+" nil define)
          ;;declarations
	  ("^[ \t]*Recursive[ \t]+Definition[ \t]+[A-Za-z0-9$_\\']+" nil defun)
          ("^[ \t]*Syntactic[ \t]+Definition[ \t]+[A-Za-z0-9$_\\']+" nil defun)
          ("^[ \t]*Tactic[ \t]+Definition[ \t]+[A-Za-z0-9$_\\']+" nil defun)
	  ("^[ \t]*Inductive[ \t]+\\(Set\\|Prop\\|Type\\)[ \t]+[A-Za-z0-9$_\\']+" nil defun)
	  ("^[ \t]*Mutual[ \t]+\\(Inductive\\|CoInductive\\)[ \t]+[A-Za-z0-9$_\\']+" nil defun)
	  ("^[ \t]*\\(Inductive\\|CoInductive\\|CoFixpoint\\|Definition\\|Local\\|Fixpoint\\|with\\|Record\\|Correctness\\)[ \t]+[A-Za-z0-9$_\\']+" nil defun)
	  ("^[ \t]*\\(Derive\\|Dependant[ \t]+Derive\\)[ \t]+\\(Inversion\\|Inversion_clear\\)[ \t]+[A-Za-z0-9$_\\']+" nil defun)
	  ("^[ \t]*\\(Variable\\|Parameter\\|Hypothesis\\).*" ":" defun)
	  ("^[ \t]*\\(Global[ \t]+Variable\\).*" ":" defun)
	  ("^[ \t]*\\(Realizer[ \t]+Program\\|Realizer\\)" nil defun)
	  ;;proofs
	  ("^[ \t]*\\(Lemma\\|Theorem\\|Remark\\|Axiom\\).*" ":" defun)
	  ("^[ \t]*Proof" nil decl)
	  ("^[ \t]*\\(Save\\|Qed\\|Defined\\|Hint\\|Immediate\\)[^.]*" nil decl)
          ;;keywords
          ("[^_]\\<\\(Case\\|Cases\\|case\\|esac\\|of\\|end\\|in\\|Match\\|with\\|Fix\\|let\\|if\\|then\\|else\\)\\>[^_]" 1 keyword)
          ("[^_]\\<\\(begin\\|assert\\|invariant\\|variant\\|for\\|while\\|do\\|done\\|state\\)\\>[^_]" 1 keyword)
          ))
))

;;; coq.el ends here

(provide 'coq)
