- The :g:`auto with zarith` tactic and variations (including :tacn:`intuition`)
  may now call the :tacn:`lia` tactic instead of :tacn:`omega`
  (when the `Omega` module is loaded);
  more goals may be automatically solved,
  fewer section variables will be captured spuriously
  (`#11018 <https://github.com/coq/coq/pull/11018>`_,
  by Vincent Laporte).
