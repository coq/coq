- **Changed:**
  The names of deprecation warnings now depend on the version
  in which they were introduced, using their "since" field.
  This enables deprecation warnings to be selectively enabled,
  disabled, or treated as an error, according to the version number
  provided in the :attr:`deprecated` attribute
  (`#17489 <https://github.com/coq/coq/pull/17489>`_,
  fixes `#16287 <https://github.com/coq/coq/issues/16287>`_,
  by Pierre Roux, reviewed by Ali Caglayan, Théo Zimmermann and Gaëtan Gilbert).
