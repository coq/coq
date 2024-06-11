- **Changed:**
  :cmd:`Fail` and :cmd:`Succeed` are considered to be "queries" with no effects on the system state.
  This may change the number to give to :cmd:`Undo`, for instance after `tac. Fail reflexivity.`
  to get back to the state before `tac.` we used to need `Undo 2.` and now need `Undo 1.`
  (`#19199 <https://github.com/coq/coq/pull/19199>`_,
  by Gaëtan Gilbert).
