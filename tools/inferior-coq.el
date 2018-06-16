;;; inferior-coq.el --- Run an inferior Coq process.
;;;
;;; Copyright (C) Marco Maggesi <maggesi@math.unifi.it>
;;; Time-stamp: "2002-02-28 12:15:04 maggesi"


;; Emacs Lisp Archive Entry
;; Filename: inferior-coq.el
;; Version: 1.0
;; Keywords: process coq
;; Author: Marco Maggesi <maggesi@math.unifi.it>
;; Maintainer: Marco Maggesi <maggesi@math.unifi.it>
;; Description: Run an inferior Coq process.
;; URL: http://www.math.unifi.it/~maggesi/
;; Compatibility: Emacs20, Emacs21, XEmacs21

;; This is free software; you can redistribute it and/or modify it under
;; the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2, or (at your option) any later
;; version.
;;
;; This is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
;; for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
;; MA 02111-1307, USA.

;;; Commentary:

;; Coq is a proof assistant (http://coq.inria.fr/).  This code run an
;; inferior Coq process and defines functions to send bits of code
;; from other buffers to the inferior process.  This is a
;; customisation of comint-mode (see comint.el).  For a more complex
;; and full featured Coq interface under Emacs look at Proof General
;; (http://zermelo.dcs.ed.ac.uk/~proofgen/).
;;
;; Written by Marco Maggesi <maggesi@math.unifi.it> with code heavly
;; borrowed from emacs cmuscheme.el
;;
;; Please send me bug reports, bug fixes, and extensions, so that I can
;; merge them into the master source.

;;; Installation:

;; You need to have gallina.el already installed (it comes with the
;; standard Coq distribution) in order to use this code.  Put this
;; file somewhere in you load-path and add the following lines in your
;; "~/.emacs":
;;
;;   (setq auto-mode-alist (cons '("\\.v$" . coq-mode) auto-mode-alist))
;;   (autoload 'coq-mode "gallina" "Major mode for editing Coq vernacular." t)
;;   (autoload 'run-coq "inferior-coq" "Run an inferior Coq process." t)
;;   (autoload 'run-coq-other-window "inferior-coq"
;;     "Run an inferior Coq process in a new window." t)
;;   (autoload 'run-coq-other-frame "inferior-coq"
;;     "Run an inferior Coq process in a new frame." t)

;;; Usage:

;; Call `M-x "run-coq'.
;;
;; Functions and key bindings (Learn more keys with `C-c C-h' or `C-h m'):
;;   C-return ('M-x coq-send-line)     send the current line.
;;   C-c C-r  (`M-x coq-send-region')  send the current region.
;;   C-c C-a  (`M-x coq-send-abort')   send the command "Abort".
;;   C-c C-t  (`M-x coq-send-restart') send the command "Restart".
;;   C-c C-s  (`M-x coq-send-show')    send the command "Show".
;;   C-c C-u  (`M-x coq-send-undo')    send the command "Undo".
;;   C-c C-v  (`M-x coq-check-region') run command "Check" on region.
;;   C-c .    (`M-x coq-come-here')    Restart and send until current point.

;;; Change Log:

;; From -0.0 to 1.0 brought into existence.


(require 'gallina)
(require 'comint)

(setq coq-program-name "coqtop")

(defgroup inferior-coq nil
  "Run a coq process in a buffer."
  :group 'coq)

(defcustom inferior-coq-mode-hook nil
  "*Hook for customising inferior-coq mode."
  :type 'hook
  :group 'coq)

(defvar inferior-coq-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m "\C-c\C-r" 'coq-send-region)
    (define-key m "\C-c\C-a" 'coq-send-abort)
    (define-key m "\C-c\C-t" 'coq-send-restart)
    (define-key m "\C-c\C-s" 'coq-send-show)
    (define-key m "\C-c\C-u" 'coq-send-undo)
    (define-key m "\C-c\C-v" 'coq-check-region)
    m))

;; Install the process communication commands in the coq-mode keymap.
(define-key coq-mode-map [(control return)] 'coq-send-line)
(define-key coq-mode-map "\C-c\C-r" 'coq-send-region)
(define-key coq-mode-map "\C-c\C-a" 'coq-send-abort)
(define-key coq-mode-map "\C-c\C-t" 'coq-send-restart)
(define-key coq-mode-map "\C-c\C-s" 'coq-send-show)
(define-key coq-mode-map "\C-c\C-u" 'coq-send-undo)
(define-key coq-mode-map "\C-c\C-v" 'coq-check-region)
(define-key coq-mode-map "\C-c." 'coq-come-here)

(defvar coq-buffer)

(define-derived-mode inferior-coq-mode comint-mode "Inferior Coq"
  "\
Major mode for interacting with an inferior Coq process.

The following commands are available:
\\{inferior-coq-mode-map}

A Coq process can be fired up with M-x run-coq.

Customisation: Entry to this mode runs the hooks on comint-mode-hook
and inferior-coq-mode-hook (in that order).

You can send text to the inferior Coq process from other buffers
containing Coq source.

Functions and key bindings (Learn more keys with `C-c C-h'):
  C-return ('M-x coq-send-line)     send the current line.
  C-c C-r  (`M-x coq-send-region')  send the current region.
  C-c C-a  (`M-x coq-send-abort')   send the command \"Abort\".
  C-c C-t  (`M-x coq-send-restart') send the command \"Restart\".
  C-c C-s  (`M-x coq-send-show')    send the command \"Show\".
  C-c C-u  (`M-x coq-send-undo')    send the command \"Undo\".
  C-c C-v  (`M-x coq-check-region') run command \"Check\" on region.
  C-c .    (`M-x coq-come-here')    Restart and send until current point.
"
  ;; Customise in inferior-coq-mode-hook
  (setq comint-prompt-regexp "^[^<]* < *")
  (coq-mode-variables)
  (setq mode-line-process '(":%s"))
  (setq comint-input-filter (function coq-input-filter))
  (setq comint-get-old-input (function coq-get-old-input)))

(defcustom inferior-coq-filter-regexp "\\`\\s *\\S ?\\S ?\\s *\\'"
  "*Input matching this regexp are not saved on the history list.
Defaults to a regexp ignoring all inputs of 0, 1, or 2 letters."
  :type 'regexp
  :group 'inferior-coq)

(defun coq-input-filter (str)
  "Don't save anything matching `inferior-coq-filter-regexp'."
  (not (string-match inferior-coq-filter-regexp str)))

(defun coq-get-old-input ()
  "Snarf the sexp ending at point."
  (save-excursion
    (let ((end (point)))
      (backward-sexp)
      (buffer-substring (point) end))))

(defun coq-args-to-list (string)
  (let ((where (string-match "[ \t]" string)))
    (cond ((null where) (list string))
	  ((not (= where 0))
	   (cons (substring string 0 where)
		 (coq-args-to-list (substring string (+ 1 where)
						 (length string)))))
	  (t (let ((pos (string-match "[^ \t]" string)))
	       (if (null pos)
		   nil
		 (coq-args-to-list (substring string pos
						 (length string)))))))))

;;;###autoload
(defun run-coq (cmd)
  "Run an inferior Coq process, input and output via buffer *coq*.
If there is a process already running in `*coq*', switch to that buffer.
With argument, allows you to edit the command line (default is value
of `coq-program-name').  Runs the hooks `inferior-coq-mode-hook'
\(after the `comint-mode-hook' is run).
\(Type \\[describe-mode] in the process buffer for a list of commands.)"

  (interactive (list (if current-prefix-arg
			 (read-string "Run Coq: " coq-program-name)
			 coq-program-name)))
  (if (not (comint-check-proc "*coq*"))
      (let ((cmdlist (coq-args-to-list cmd)))
	(set-buffer (apply 'make-comint "coq" (car cmdlist)
			   nil (cdr cmdlist)))
	(inferior-coq-mode)))
  (setq coq-program-name cmd)
  (setq coq-buffer "*coq*")
  (switch-to-buffer "*coq*"))
;;;###autoload (add-hook 'same-window-buffer-names "*coq*")

;;;###autoload
(defun run-coq-other-window (cmd)
  "Run an inferior Coq process, input and output via buffer *coq*.
If there is a process already running in `*coq*', switch to that buffer.
With argument, allows you to edit the command line (default is value
of `coq-program-name').  Runs the hooks `inferior-coq-mode-hook'
\(after the `comint-mode-hook' is run).
\(Type \\[describe-mode] in the process buffer for a list of commands.)"

  (interactive (list (if current-prefix-arg
			 (read-string "Run Coq: " coq-program-name)
			 coq-program-name)))
  (if (not (comint-check-proc "*coq*"))
      (let ((cmdlist (coq-args-to-list cmd)))
	(set-buffer (apply 'make-comint "coq" (car cmdlist)
			   nil (cdr cmdlist)))
	(inferior-coq-mode)))
  (setq coq-program-name cmd)
  (setq coq-buffer "*coq*")
  (pop-to-buffer "*coq*"))
;;;###autoload (add-hook 'same-window-buffer-names "*coq*")

(defun run-coq-other-frame (cmd)
  "Run an inferior Coq process, input and output via buffer *coq*.
If there is a process already running in `*coq*', switch to that buffer.
With argument, allows you to edit the command line (default is value
of `coq-program-name').  Runs the hooks `inferior-coq-mode-hook'
\(after the `comint-mode-hook' is run).
\(Type \\[describe-mode] in the process buffer for a list of commands.)"

  (interactive (list (if current-prefix-arg
			 (read-string "Run Coq: " coq-program-name)
			 coq-program-name)))
  (if (not (comint-check-proc "*coq*"))
      (let ((cmdlist (coq-args-to-list cmd)))
	(set-buffer (apply 'make-comint "coq" (car cmdlist)
			   nil (cdr cmdlist)))
	(inferior-coq-mode)))
  (setq coq-program-name cmd)
  (setq coq-buffer "*coq*")
  (switch-to-buffer-other-frame "*coq*"))

(defun switch-to-coq (eob-p)
  "Switch to the coq process buffer.
With argument, position cursor at end of buffer."
  (interactive "P")
  (if (get-buffer coq-buffer)
      (pop-to-buffer coq-buffer)
      (error "No current process buffer.  See variable `coq-buffer'"))
  (cond (eob-p
	 (push-mark)
	 (goto-char (point-max)))))

(defun coq-send-region (start end)
  "Send the current region to the inferior Coq process."
  (interactive "r")
  (comint-send-region (coq-proc) start end)
  (comint-send-string (coq-proc) "\n"))

(defun coq-send-line ()
  "Send the current line to the Coq process."
  (interactive)
  (save-excursion
    (end-of-line)
    (let ((end (point)))
      (beginning-of-line)
      (coq-send-region (point) end)))
  (forward-line 1))

(defun coq-send-abort ()
  "Send the command \"Abort.\" to the inferior Coq process."
  (interactive)
  (comint-send-string (coq-proc) "Abort.\n"))

(defun coq-send-restart ()
  "Send the command \"Restart.\" to the inferior Coq process."
  (interactive)
  (comint-send-string (coq-proc) "Restart.\n"))

(defun coq-send-undo ()
  "Reset coq to the initial state and send the region between the
   beginning of file and the point."
  (interactive)
  (comint-send-string (coq-proc) "Undo.\n"))

(defun coq-check-region (start end)
  "Run the commmand \"Check\" on the current region."
  (interactive "r")
  (comint-proc-query (coq-proc)
		     (concat "Check "
			     (buffer-substring start end)
			     ".\n")))

(defun coq-send-show ()
  "Send the command \"Show.\" to the inferior Coq process."
  (interactive)
  (comint-send-string (coq-proc) "Show.\n"))

(defun coq-come-here ()
  "Reset coq to the initial state and send the region between the
   beginning of file and the point."
  (interactive)
  (comint-send-string (coq-proc) "Reset Initial.\n")
  (coq-send-region 1 (point)))

(defvar coq-buffer nil "*The current coq process buffer.")

(defun coq-proc ()
  "Return the current coq process.  See variable `coq-buffer'."
  (let ((proc (get-buffer-process (if (eq major-mode 'inferior-coq-mode)
				      (current-buffer)
				      coq-buffer))))
    (or proc
	(error "No current process.  See variable `coq-buffer'"))))

(defcustom inferior-coq-load-hook nil
  "This hook is run when inferior-coq is loaded in.
This is a good place to put keybindings."
  :type 'hook
  :group 'inferior-coq)
	
(run-hooks 'inferior-coq-load-hook)

(provide 'inferior-coq)
