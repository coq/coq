((coq-mode . ((eval . (let ((default-directory (locate-dominating-file
						buffer-file-name ".dir-locals.el")))
			(setq-local coq-prog-args `("-coqlib" ,(expand-file-name "..") "-R" ,(expand-file-name ".") "Coq"))
			(setq-local coq-prog-name (expand-file-name "../bin/coqtop")))))))
