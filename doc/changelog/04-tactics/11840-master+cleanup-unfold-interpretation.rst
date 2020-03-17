- **Added:**
  New tactic argument type `evaluable_ref` capturing the kind of
  argument supported by :tacn:`unfold` or by the `delta` flag;
  moreover, tactic :tacn:`unfold` now accepts opaque definitions and
  axioms when used in Ltac definitions
  (`#11840 <https://github.com/coq/coq/pull/11840>`_,
  by Hugo Herbelin, fixes `#11727 <https://github.com/coq/coq/issues/11727>`_).
