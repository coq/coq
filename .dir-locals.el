((nil . ((eval . (setq default-directory (locate-dominating-file
                                          buffer-file-name
                                          ".dir-locals.el")
                       tags-file-name (concat default-directory
                                          "TAGS")
                       camldebug-command-name (concat
                                          default-directory "dev/ocamldebug-coq")
)))))