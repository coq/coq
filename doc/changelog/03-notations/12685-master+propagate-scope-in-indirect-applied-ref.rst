- **Changed:**
  Scope information is propagated in indirect applications to a
  reference prefixed with :g:`@@`; this covers for instance the case
  :g:`r.(@@p) t` where scope information from :g:`p` is now taken into
  account for interpreting :g:`t` (`#12685
  <https://github.com/coq/coq/pull/12685>`_, by Hugo Herbelin).
