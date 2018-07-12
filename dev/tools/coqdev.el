;;; coqdev.el --- Emacs helpers for Coq development  -*- lexical-binding:t -*-

;; Copyright (C) 2018 The Coq Development Team

;; Maintainer: coqdev@inria.fr

;;; Commentary:

;; Helpers to set compilation commands, proof general variables, etc
;; for Coq development

;; You can disable individual features without editing this file by
;; using `remove-hook', for instance
;; (remove-hook 'hack-local-variables-hook #'coqdev-setup-compile-command)

;;; Installation:

;; To use this, with coqdev.el located at /path/to/coqdev.el, add the
;; following to your init:

;; (add-to-list 'load-path "/path/to/coqdev/")
;; (require 'coqdev)

;; If you load this file from a git repository, checking out an old
;; commit will make it disappear and cause errors for your Emacs
;; startup.  To ignore those errors use (require 'coqdev nil t).  If you
;; check out a malicious commit Emacs startup would allow it to run
;; arbitrary code, to avoid this you can copy coqdev.el to any
;; location and adjust the load path accordingly (of course if you run
;; ./configure to compile Coq it is already too late).

;;; Code:

(defun coqdev-default-directory ()
  "Return the Coq repository containing `default-directory'."
  (let ((dir (locate-dominating-file default-directory "META.coq.in")))
    (when dir (expand-file-name dir))))

(defun coqdev-setup-compile-command ()
  "Setup `compile-command' for Coq development."
  (let ((dir (coqdev-default-directory)))
    ;; we add a space at the end to make it easy to add arguments (eg -j or target)
    (when dir (setq-local compile-command (concat "make -C " (shell-quote-argument dir) " ")))))
(add-hook 'hack-local-variables-hook #'coqdev-setup-compile-command)

(defvar camldebug-command-name) ; from camldebug.el (caml package)
(defvar ocamldebug-command-name) ; from ocamldebug.el (tuareg package)
(defun coqdev-setup-camldebug ()
  "Setup ocamldebug for Coq development.

Specifically `camldebug-command-name' and `ocamldebug-command-name'."
  (let ((dir (coqdev-default-directory)))
    (when dir
      (setq-local camldebug-command-name
                  (concat dir "dev/ocamldebug-coq"))
      (setq-local ocamldebug-command-name
                  (concat dir "dev/ocamldebug-coq")))))
(add-hook 'hack-local-variables-hook #'coqdev-setup-camldebug)

(defun coqdev-setup-tags ()
  "Setup `tags-file-name' for Coq development."
  (let ((dir (coqdev-default-directory)))
    (when dir (setq-local tags-file-name (concat dir "TAGS")))))
(add-hook 'hack-local-variables-hook #'coqdev-setup-tags)

(defvar coq-prog-args)
(defvar coq-prog-name)

;; Lets us detect whether there are file local variables
;; even though PG sets it with `setq' when there's a _Coqproject.
;; Also makes sense generally, so might make it into PG someday.
(make-variable-buffer-local 'coq-prog-args)
(setq-default coq-prog-args nil)

(defun coqdev-setup-proofgeneral ()
  "Setup Proofgeneral variables for Coq development.

Note that this function is executed before _Coqproject is read if it exists."
  (let ((dir (coqdev-default-directory)))
    (when dir
      (unless coq-prog-args
        (setq coq-prog-args
              `("-coqlib" ,dir "-R" ,(concat dir "plugins")
                "Coq" "-R" ,(concat dir "theories")
                "Coq")))
      (setq-local coq-prog-name (concat dir "bin/coqtop")))))
(add-hook 'hack-local-variables-hook #'coqdev-setup-proofgeneral)

;; This Elisp snippet adds a regexp parser for the format of Anomaly
;; backtraces (coqc -bt ...), to the error parser of the Compilation
;; mode (C-c C-c: "Compile command: ..."). File locations in traces
;; are recognized and can be jumped from easily in the *compilation*
;; buffer.
(defvar compilation-error-regexp-alist-alist)
(defvar compilation-error-regexp-alist)
(with-eval-after-load 'compile
  (add-to-list
   'compilation-error-regexp-alist-alist
   '(coq-backtrace
     "^ *\\(?:raise\\|frame\\) @ file \\(\"?\\)\\([^,\" \n\t<>]+\\)\\1,\
      lines? \\([0-9]+\\)-?\\([0-9]+\\)?\\(?:$\\|,\
      \\(?: characters? \\([0-9]+\\)-?\\([0-9]+\\)?:?\\)?\\)"
     2 (3 . 4) (5 . 6)))
  (add-to-list 'compilation-error-regexp-alist 'coq-backtrace))

(defvar bug-reference-bug-regexp)
(defvar bug-reference-url-format)
(defun coqdev-setup-bug-reference-mode ()
  "Setup `bug-reference-bug-regexp' and `bug-reference-url-format' for Coq.

This does not enable `bug-reference-mode'."
  (let ((dir (coqdev-default-directory)))
    (when dir
      (setq-local bug-reference-bug-regexp "#\\(?2:[0-9]+\\)")
      (setq-local bug-reference-url-format "https://github.com/coq/coq/issues/%s"))))
(add-hook 'hack-local-variables-hook #'coqdev-setup-bug-reference-mode)

(defun coqdev-sphinx-quote-coq-refman-region (left right &optional offset beg end)
  "Add LEFT and RIGHT around the BEG..END.
Leave the point after RIGHT.  BEG and END default to the bounds
of the current region.  Leave point OFFSET characters after the
left quote (if OFFSET is nil, leave the point after the right
quote)."
  (unless beg
    (if (region-active-p)
        (setq beg (region-beginning) end (region-end))
      (setq beg (point) end nil)))
  (save-excursion
    (goto-char (or end beg))
    (insert right))
  (save-excursion
    (goto-char beg)
    (insert left))
  (if (and end (not offset)) ;; Second test handles the ::`` case
      (goto-char (+ end (length left) (length right)))
    (goto-char (+ beg (or offset (length left))))))

(defun coqdev-sphinx-rst-coq-action ()
  "Insert a Sphinx role template or quote the current region."
  (interactive)
  (pcase (read-char "Command [gntm:`]?")
    (?g (coqdev-sphinx-quote-coq-refman-region ":g:`" "`"))
    (?n (coqdev-sphinx-quote-coq-refman-region ":n:`" "`"))
    (?t (coqdev-sphinx-quote-coq-refman-region ":token:`" "`"))
    (?m (coqdev-sphinx-quote-coq-refman-region ":math:`" "`"))
    (?: (coqdev-sphinx-quote-coq-refman-region "::`" "`" 1))
    (?` (coqdev-sphinx-quote-coq-refman-region "``" "``"))))

(provide 'coqdev)
;;; coqdev ends here
