;; coq-font-lock.el --- Coq syntax highlighting for Emacs - compatibilty code
;; Pierre Courtieu, may 2009
;;
;; Authors: Pierre Courtieu
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>

;; This is copy paste from ProofGeneral by David Aspinall
;; <David.Aspinall@ed.ac.uk>. ProofGeneral is under GPL and Copyright
;; (C) LFCS Edinburgh.


;;; Commentary:
;; This file contains the code necessary to coq-syntax.el and
;; coq-db.el from ProofGeneral. It is also pocked from ProofGeneral.


;;; History:
;; First created from ProofGeneral may 28th 2009


;;; Code:

(setq coq-version-is-V8-1 t)
(defun coq-build-regexp-list-from-db (db &optional filter)
  "Take a keyword database DB and return the list of regexps for font-lock.
If non-nil Optional argument FILTER is a function applying to each line of DB.
For each line if FILTER returns nil, then the keyword is not added to the
regexp.  See `coq-syntax-db' for DB structure."
  (let ((l db) (res ()))
    (while l
      (let* ((hd (car l)) (tl (cdr l))	; hd is the first infos list
             (e1 (car hd)) (tl1 (cdr hd)) ; e1 = menu entry
             (e2 (car tl1)) (tl2 (cdr tl1)) ; e2 = abbreviation
             (e3 (car tl2)) (tl3 (cdr tl2)) ; e3 = completion
             (e4 (car-safe tl3)) (tl4 (cdr-safe tl3)) ; e4 = state changing
             (e5 (car-safe tl4)) (tl5 (cdr-safe tl4)) ; e5 = colorization string
             )
        ;; TODO delete doublons
        (when (and e5 (or (not filter) (funcall filter hd)))
          (setq res (nconc res (list e5)))) ; careful: nconc destructive!
        (setq l tl)))
    res
    ))
(defun filter-state-preserving (l)
  ; checkdoc-params: (l)
  "Not documented."
  (not (nth 3 l))) ; fourth argument is nil --> state preserving command

(defun filter-state-changing (l)
  ; checkdoc-params: (l)
  "Not documented."
  (nth 3 l)) ; fourth argument is nil --> state preserving command

;; Generic font-lock

(defvar proof-id "\\(\\w\\(\\w\\|\\s_\\)*\\)"
  "A regular expression for parsing identifiers.")

;; For font-lock, we treat ,-separated identifiers as one identifier
;; and refontify commata using \{proof-zap-commas}.

(defun proof-anchor-regexp (e)
  "Anchor (\\`) and group the regexp E."
  (concat "\\`\\(" e "\\)"))

(defun proof-ids (proof-id &optional sepregexp)
  "Generate a regular expression for separated lists of identifiers PROOF-ID.
Default is comma separated, or SEPREGEXP if set."
  (concat proof-id "\\(\\s-*"   (or sepregexp ",") "\\s-*"
	  proof-id "\\)*"))

(defun proof-ids-to-regexp (l)
  "Maps a non-empty list of tokens `L' to a regexp matching any element."
  (if (featurep 'xemacs)
      (mapconcat (lambda (s) (concat "\\_<" s "\\_>")) l "\\|") ;; old version
    (concat "\\_<\\(?:" (mapconcat 'identity l "\\|") "\\)\\_>")))

;; TODO: get rid of this list.  Does 'default work widely enough
;; by now?
(defconst pg-defface-window-systems
  '(x            ;; bog standard
    mswindows    ;; Windows
    w32	         ;; Windows
    gtk          ;; gtk emacs (obsolete?)
    mac          ;; used by Aquamacs
    carbon       ;; used by Carbon XEmacs
    ns           ;; NeXTstep Emacs (Emacs.app)
    x-toolkit)   ;; possible catch all (but probably not)
  "A list of possible values for variable `window-system'.
If you are on a window system and your value of variable
`window-system' is not listed here, you may not get the correct
syntax colouring behaviour.")

(defmacro proof-face-specs (bl bd ow)
  "Return a spec for `defface' with BL for light bg, BD for dark, OW o/w."
  `(append
    (apply 'append
     (mapcar
     (lambda (ty) (list
		     (list (list (list 'type ty) '(class color)
			   (list 'background 'light))
			   (quote ,bl))
		     (list (list (list 'type ty) '(class color)
				 (list 'background 'dark))
			   (quote ,bd))))
     pg-defface-window-systems))
    (list (list t (quote ,ow)))))

;;A new face for tactics
(defface coq-solve-tactics-face
  (proof-face-specs
   (:foreground "forestgreen" t) ; for bright backgrounds
   (:foreground "forestgreen"  t) ; for dark backgrounds
   ()) ; for black and white
  "Face for names of closing tactics in proof scripts."
  :group 'proof-faces)

;;A new face for tactics which fail when they don't kill the current goal
(defface coq-solve-tactics-face
  (proof-face-specs
   (:foreground "red" t) ; for bright backgrounds
   (:foreground "red"  t) ; for dark backgrounds
   ()) ; for black and white
  "Face for names of closing tactics in proof scripts."
  :group 'proof-faces)


(defconst coq-solve-tactics-face 'coq-solve-tactics-face
  "Expression that evaluates to a face.
Required so that 'proof-solve-tactics-face is a proper facename")

(defconst proof-tactics-name-face 'coq-solve-tactics-face)
(defconst proof-tacticals-name-face 'coq-solve-tactics-face)

(provide 'coq-font-lock)
;;; coq-font-lock.el ends here
