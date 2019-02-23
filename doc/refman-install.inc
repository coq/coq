(rule
 (targets sphinx_build/html/index.html)
 (deps sphinx_build)
 (action (run true)))

(install
 (section doc)
 (package coq-refman)
 (files ("sphinx_build/html/index.html" as "refman/html/index.html")))
