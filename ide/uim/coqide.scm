;;; coqide.scm -- Emacs-style Latin characters translation
;;;
;;; Copyright (c) 2003-2009 uim Project http://code.google.com/p/uim/
;;;
;;; All rights reserved.
;;;
;;; Redistribution and use in source and binary forms, with or without
;;; modification, are permitted provided that the following conditions
;;; are met:
;;; 1. Redistributions of source code must retain the above copyright
;;;    notice, this list of conditions and the following disclaimer.
;;; 2. Redistributions in binary form must reproduce the above copyright
;;;    notice, this list of conditions and the following disclaimer in the
;;;    documentation and/or other materials provided with the distribution.
;;; 3. Neither the name of authors nor the names of its contributors
;;;    may be used to endorse or promote products derived from this software
;;;    without specific prior written permission.
;;;
;;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS ``AS IS'' AND
;;; ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
;;; IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;; ARE DISCLAIMED.  IN NO EVENT SHALL THE COPYRIGHT HOLDERS OR CONTRIBUTORS BE LIABLE
;;; FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
;;; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
;;; OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
;;; HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
;;; LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
;;; OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
;;; SUCH DAMAGE.
;;;;

;; This input method implements character composition rules for the
;; Latin letters used in European languages.  The rules, defined in
;; the file coqide-rules.scm, have been adapted from GNU Emacs 22.

(require "util.scm")
(require "rk.scm")
(require "coqide-rules.scm")
(require-custom "generic-key-custom.scm")
(require-custom "coqide-custom.scm")

(define coqide-context-rec-spec
  (append
   context-rec-spec
   '((on	 #f)
     (rkc	 #f)
     (show-cands #f))))
(define-record 'coqide-context coqide-context-rec-spec)
(define coqide-context-new-internal coqide-context-new)

(define (coqide-context-new id im)
  (let ((lc (coqide-context-new-internal id im))
	(rkc (rk-context-new (symbol-value coqide-rules) #f #f)))
    (coqide-context-set-widgets! lc coqide-widgets)
    (coqide-context-set-rkc! lc rkc)
    lc))

(define (coqide-current-translation lc)
  (let ((rkc (coqide-context-rkc lc)))
    (or (rk-peek-terminal-match rkc)
	(and (not (null? (rk-context-seq rkc)))
	     (list (rk-pending rkc))))))

(define (coqide-current-string lc)
  (let ((trans (coqide-current-translation lc)))
    (if trans (car trans) "")))

(define (coqide-context-clear lc)
  (rk-flush (coqide-context-rkc lc)))

(define (coqide-context-flush lc)
  (let ((str (coqide-current-string lc)))
    (if (not (equal? str "")) (im-commit lc str))
    (coqide-context-clear lc)))

(define (coqide-open-candidates-window lc height)
  (if (coqide-context-show-cands lc)
      (im-deactivate-candidate-selector lc))
  (im-activate-candidate-selector lc height height)
  (im-select-candidate lc 0)
  (coqide-context-set-show-cands! lc #t))

(define (coqide-close-candidates-window lc)
  (if (coqide-context-show-cands lc)
      (im-deactivate-candidate-selector lc))
  (coqide-context-set-show-cands! lc #f))

(define (coqide-update-preedit lc)
  (if (coqide-context-on lc)
      (let ((trans (coqide-current-translation lc))
	    (ltrans 0))
	(im-clear-preedit lc)
	(if trans
	    (begin (im-pushback-preedit lc
					preedit-underline
					(car trans))
		   (set! ltrans (length trans))))
	(im-pushback-preedit lc
			     preedit-cursor
			     "")
	(im-update-preedit lc)
	(if (> ltrans 1)
	    (coqide-open-candidates-window lc ltrans)
	    (coqide-close-candidates-window lc)))))

(define (coqide-prepare-activation lc)
  (coqide-context-flush lc)
  (coqide-update-preedit lc))

(register-action 'action_coqide_off
		 (lambda (lc)
		   (list
		    'off
		    "a"
		    (N_ "CoqIDE mode off")
		    (N_ "CoqIDE composition off")))
		 (lambda (lc)
		   (not (coqide-context-on lc)))
		 (lambda (lc)
		   (coqide-prepare-activation lc)
		   (coqide-context-set-on! lc #f)))

(register-action 'action_coqide_on
		 (lambda (lc)
		   (list
		    'on
		    "à"
		    (N_ "CoqIDE mode on")
		    (N_ "CoqIDE composition on")))
		 (lambda (lc)
		   (coqide-context-on lc))
		 (lambda (lc)
		   (coqide-prepare-activation lc)
		   (coqide-context-set-on! lc #t)))

(define coqide-input-mode-actions
  '(action_coqide_off action_coqide_on))

(define coqide-widgets '(widget_coqide_input_mode))

(define default-widget_coqide_input_mode 'action_coqide_on)

(register-widget 'widget_coqide_input_mode
		 (activity-indicator-new coqide-input-mode-actions)
		 (actions-new coqide-input-mode-actions))

(define coqide-context-list '())

(define (coqide-init-handler id im arg)
  (let ((lc (coqide-context-new id im)))
    (set! coqide-context-list (cons lc coqide-context-list))
    lc))

(define (coqide-release-handler lc)
  (let ((rkc (coqide-context-rkc lc)))
    (set! coqide-context-list
	  ;; (delete lc coqide-context-list eq?) does not work
	  (remove (lambda (c) (eq? (coqide-context-rkc c) rkc))
		  coqide-context-list))))

(define coqide-control-key?
  (let ((shift-or-no-modifier? (make-key-predicate '("<Shift>" ""))))
    (lambda (key key-state)
      (not (shift-or-no-modifier? -1 key-state)))))

(define (coqide-proc-on-state lc key key-state)
  (let ((rkc (coqide-context-rkc lc))
	(cur-trans (coqide-current-translation lc)))
    (cond

     ((or (coqide-off-key? key key-state)
	  (and coqide-esc-turns-off? (eq? key 'escape)))
      (coqide-context-flush lc)
      (if (eq? key 'escape)
	  (im-commit-raw lc))
      (coqide-context-set-on! lc #f)
      (coqide-close-candidates-window lc)
      (im-clear-preedit lc)
      (im-update-preedit lc))

     ((coqide-backspace-key? key key-state)
      (if (not (rk-backspace rkc))
	  (im-commit-raw lc)))

     ((coqide-control-key? key key-state)
      (coqide-context-flush lc)
      (im-commit-raw lc))

     ((and (ichar-numeric? key)
	   (coqide-context-show-cands lc)
	   (let ((idx (- (numeric-ichar->integer key) 1)))
	     (if (= idx -1) (set! idx 9))
	     (and (>= idx 0) (< idx (length cur-trans))
		  (begin
		    (im-commit lc (nth idx cur-trans))
		    (coqide-context-clear lc)
		    #t)))))

     (else
      (let* ((key-str (if (symbol? key)
			  (symbol->string key)
			  (charcode->string key)))
	     (cur-seq (rk-context-seq rkc))
	     (res (rk-push-key! rkc key-str))
	     (new-seq (rk-context-seq rkc))
	     (new-trans (coqide-current-translation lc)))
	(if (equal? new-seq (cons key-str cur-seq))
	    (if (not (or (rk-partial? rkc) (> (length new-trans) 1)))
		(begin (im-commit lc (car (rk-peek-terminal-match rkc)))
		       (coqide-context-clear lc)))
	    (begin (if (not (null? cur-seq)) (im-commit lc (car cur-trans)))
		   (if (null? new-seq) (im-commit-raw lc)))))))))

(define (coqide-proc-off-state lc key key-state)
  (if (coqide-on-key? key key-state)
      (coqide-context-set-on! lc #t)
      (im-commit-raw lc)))

(define (coqide-key-press-handler lc key key-state)
  (if (coqide-context-on lc)
      (coqide-proc-on-state lc key key-state)
      (coqide-proc-off-state lc key key-state))
  (coqide-update-preedit lc))

(define (coqide-key-release-handler lc key key-state)
  (if (or (ichar-control? key)
	  (not (coqide-context-on lc)))
      ;; don't discard key release event for apps
      (im-commit-raw lc)))

(define (coqide-reset-handler lc)
  (coqide-context-clear lc))

(define (coqide-get-candidate-handler lc idx accel-enum-hint)
  (let* ((candidates (coqide-current-translation lc))
	 (candidate (nth idx candidates)))
    (list candidate (digit->string (+ idx 1)) "")))

;; Emacs does nothing on focus-out
;; TODO: this should be configurable
(define (coqide-focus-out-handler lc)
  #f)

(define (coqide-place-handler lc)
  (coqide-update-preedit lc))

(define (coqide-displace-handler lc)
  (coqide-context-flush lc)
  (coqide-update-preedit lc))

(register-im
 'coqide
 ""
 "UTF-8"
 coqide-im-name-label
 coqide-im-short-desc
 #f
 coqide-init-handler
 coqide-release-handler
 context-mode-handler
 coqide-key-press-handler
 coqide-key-release-handler
 coqide-reset-handler
 coqide-get-candidate-handler
 #f
 context-prop-activate-handler
 #f
 #f
 coqide-focus-out-handler
 coqide-place-handler
 coqide-displace-handler
)

;; Local Variables:
;; mode: scheme
;; coding: utf-8
;; End:
