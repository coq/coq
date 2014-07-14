;; EMACS CONFIGURATION FOR COQ DEVELOPPERS This configuration will be
;; executed for each opened file under coq root directory.
((nil
  . ((eval
      . (progn
	  ;; coq root directory (ending with slash)
	  (let ((coq-root-directory (when buffer-file-name
				      (locate-dominating-file
				       buffer-file-name
				       ".dir-locals.el")))
		(coq-project-find-file
		 (and (boundp 'coq-project-find-file) coq-project-find-file)))
	    ;; coq tags file and coq debugger executable
	    (set (make-local-variable 'tags-file-name)
		 (concat coq-root-directory "TAGS"))
	    (setq camldebug-command-name (concat coq-root-directory
						 "dev/ocamldebug-coq"))

	    ;; Setting the compilation directory to coq root. This is
	    ;; mutually exclusive with the setting of default-directory
	    ;; below. Also setting the path for next error.
	    (unless coq-project-find-file
	      (set (make-local-variable 'compile-command)
		   (concat "make -C " coq-root-directory))
	      (set (make-local-variable 'compilation-search-path)
		   (cons coq-root-directory nil)))

	    ;; Set default directory to coq root ONLY IF variable
	    ;; coq-project-find-file is non nil. This should remain a
	    ;; user preference and not be set by default. This setting
	    ;; is redundant with compile-command above as M-x compile
	    ;; always CD's to default directory. To enable it add this
	    ;; to your emacs config: (setq coq-project-find-file t)
	    (when coq-project-find-file
	      (setq default-directory coq-root-directory))))
      ))
  ))
