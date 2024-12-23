- **Fixed:**
  Some cases where :tacn:`simpl` and :tacn:`cbn` simplified a
  primitive projection even though the `simpl never` modifier (see
  :cmd:`Arguments`) was set for the projection
  (`#15661 <https://github.com/coq/coq/pull/15661>`_,
  fixes `#5698 <https://github.com/coq/coq/issues/5698>`_,
  by Hugo Herbelin).
