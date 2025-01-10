- **Changed:**
  Typeclasses queries of classes that are declared with the options
  `Typeclasses Strict Resolution` and `Typeclasses Unique Instances`
  enabled are resolved independently of other queries, allowing them
  to succeed even when the remaining queries fail
  (`#18762 <https://github.com/coq/coq/pull/18762>`_,
  by Jan-Oliver Kaiser).
