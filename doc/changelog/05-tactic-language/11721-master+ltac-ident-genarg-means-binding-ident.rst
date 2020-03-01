- **Changed:**
  All uses of ``ident(x)`` or ``intropatterns(pat)`` in a new tactic
  definition now declare the corresponding variables as binding
  variables. (If this is not what is intended, one should use ``hyp(x)``,
  for a variable of the context, or ``reference(x)``, for a global
  reference, or ``quantified_hypothesis(x)``, for a variable which is
  either in the context or quantified in the current goal, or
  ``pre_ident(x)`` for an uninterpreted ident.). Hence :g:`Ltac f := intro x;
  apply x` now succeeds like :g:`Ltac f := intros x; apply x` always has.
  This is potentially source of rare incompatibilities
  (`#11721 <https://github.com/coq/coq/pull/11721>`_,
  by Hugo Herbelin).
