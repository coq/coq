;;; coqide-custom.scm -- customization variables for coqide.scm
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

(require "i18n.scm")

(define coqide-im-name-label (N_ "CoqIDE"))
(define coqide-im-short-desc (N_ "Emacs-style Latin characters input"))
(define coqide-im-long-desc (N_ "An input method for entering Latin letters used in European languages with the key translations adopted in Emacs."))

(define-custom-group 'coqide
  coqide-im-name-label
  coqide-im-short-desc)

(define-custom-group 'coqide-properties
  (N_ "Properties")
  (N_ "long description will be here."))

(define-custom 'coqide-rules 'coqide-rules-latin-ltx
  '(coqide coqide-properties)
  (list 'choice
	(list 'coqide-rules-british
	      (N_ "British")
	      (N_ "long description will be here."))
	(list 'coqide-rules-english-dvorak
	      (N_ "English Dvorak")
	      (N_ "long description will be here."))
	(list 'coqide-rules-latin-ltx
	      (N_ "LaTeX style")
	      (N_ "long description will be here.")))
  (N_ "Latin characters keyboard layout")
  (N_ "long description will be here."))

(custom-add-hook 'coqide-rules
		 'custom-set-hooks
		 (lambda ()
		   (map (lambda (lc)
			  (let ((new-rkc (rk-context-new
					  (symbol-value coqide-rules) #f #f)))
			    (coqide-context-flush lc)
			    (coqide-update-preedit lc)
			    (coqide-context-set-rkc! lc new-rkc)))
			coqide-context-list)))

;; For VI users.
(define-custom 'coqide-esc-turns-off? #f
  '(coqide coqide-properties)
  '(boolean)
  (N_ "ESC turns off composition mode (for vi users)")
  (N_ "long description will be here."))


(define-custom-group 'coqide-keys
  (N_ "CoqIDE key bindings")
  (N_ "long description will be here."))

(define-custom 'coqide-on-key '("<Control>\\")
  '(coqide coqide-keys)
  '(key)
  (N_ "CoqIDE on")
  (N_ "long description will be here"))

(define-custom 'coqide-off-key '("<Control>\\")
  '(coqide coqide-keys)
  '(key)
  (N_ "CoqIDE off")
  (N_ "long description will be here"))

(define-custom 'coqide-backspace-key '(generic-backspace-key)
  '(coqide coqide-keys)
  '(key)
  (N_ "CoqIDE backspace")
  (N_ "long description will be here"))

;; Local Variables:
;; mode: scheme
;; coding: utf-8
;; End:
