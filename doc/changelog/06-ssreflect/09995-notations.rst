- `inE` now expands `y \in r x` when `r` is a `simpl_rel`.
  New `{pred T}` notation for a `pred T` alias in the `pred_sort` coercion
  class, simplified `predType` interface: `pred_class` and `mkPredType`
  deprecated, `{pred T}` and `PredType` should be used instead.
  `if c return t then ...` now expects `c` to be a variable bound in `t`.
  New `nonPropType` interface matching types that do _not_ have sort `Prop`.
  New `relpre R f` definition for the preimage of a relation R under f
  (`#9995 <https://github.com/coq/coq/pull/9995>`_, by Georges Gonthier).
