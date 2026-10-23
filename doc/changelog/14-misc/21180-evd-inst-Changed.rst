- **Changed:**
  Rocq can now instantiate an evar `?a` with a term of the form `?b x` where `x` is not in the scope of `?a`. This allows unifying, e.g. `forall x : ?T, f (?a x)` with `forall _ : ?T, ?b`. In particular, it makes every tactic more powerful
  (`#21180 <https://github.com/rocq-prover/rocq/pull/21180>`_,
  by Quentin Vermande).
