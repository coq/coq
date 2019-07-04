- Require parentheses around nested disjunctive patterns, so that pattern and
  term syntax are consistent; match branch patterns no longer require
  parentheses for notation at level 100 or more. Incompatibilities:

  + in :g:`match p with (_, (0|1)) => ...` parentheses may no longer be
    omitted around :n:`0|1`.
  + notation :g:`(p | q)` now potentially clashes with core pattern syntax,
    and should be avoided. ``-w disj-pattern-notation`` flags such :cmd:`Notation`.

  See :ref:`extendedpatternmatching` for details
  (`#10167 <https://github.com/coq/coq/pull/10167>`_,
  by Georges Gonthier).
