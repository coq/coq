- The :tacn:`zify` tactic is now aware of `Pos.pred_double`, `Pos.pred_N`,
  `Pos.of_nat`, `Pos.add_carry`, `Pos.pow`, `Pos.square`, `Z.pow`, `Z.double`,
  `Z.pred_double`, `Z.succ_double`, `Z.square`, `Z.div2`, and `Z.quot2`.
  Injections for internal definitions in `ZifyBool.v` (`isZero` and `isLeZero`)
  are also added to help users to declare new :tacn:`zify` class instances using
  Micromega tactics.
  (`#10998 <https://github.com/coq/coq/pull/10998>`_, by Kazuhiko Sakaguchi).
