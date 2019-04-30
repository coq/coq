Unreleased changes
==================

<!-- Until https://github.com/coq/coq/pull/9964 is merged, we continue
     adding changelog entry here. -->

**Kernel**


**Specification language, type inference**


**Notations**


**Tactics**

- New variant change_no_check of change (usable as a documented
  replacement of convert_concl_no_check).

**Tactic language**


**SSReflect**

- `inE` now expands `y \in r x` when `r` is a `simpl_rel`.

- New `{pred T}` notation for a `pred T` alias in the `pred_sort` coercion
  class, simplified `predType` interface: `pred_class` and `mkPredType`
  deprecated, `{pred T}` and `PredType` should be used instead.

- `if c return t then ...` now expects `c` to be a variable bound in `t`.

- New `nonPropType` interface matching types that do _not_ have sort `Prop`.

- New `relpre R f` definition for the preimage of a relation R under f.


**Commands and options**


**Tools**


**CoqIDE**


**Standard library**

- Added Coq.Structures.EqualitiesFacts.PairUsualDecidableTypeFull


**Infrastructure and dependencies**


**Miscellaneous**


Released changes
================

See <https://coq.github.io/doc/master/refman/changes.html>.
