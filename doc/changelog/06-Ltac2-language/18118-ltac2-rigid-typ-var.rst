- **Changed:**
  explicit type variables are rigid, such that annotations like
  `Ltac2 id (x:'a) := ...` ensure that `id` will be polymorphic.
  Previously for instance `Ltac2 bad_id (x:'a) : 'b := x.` would be accepted
  (`#18118 <https://github.com/coq/coq/pull/18118>`_,
  by Gaëtan Gilbert).
