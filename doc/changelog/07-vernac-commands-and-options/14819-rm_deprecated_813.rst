- **Removed:**
  boolean attributes ``monomorphic``, ``noncumulative`` and ``notemplate`` that were replaced by ``polymorphic=no``, ``cumulative=no`` and ``template=no`` in 8.13.
  (`#14819 <https://github.com/coq/coq/pull/14819>`_,
  by Pierre Roux).
- **Removed:**
  command ``Grab Existential Variables`` that was deprecated in 8.13. Use :cmd:`Unshelve` that is mostly equivalent, up to the reverse order of the resulting subgoals.
  (`#14819 <https://github.com/coq/coq/pull/14819>`_,
  by Pierre Roux).
- **Removed:**
  command ``Existential`` that was deprecated in 8.13. Use :cmd:`Unshelve` and :tacn:`exact`.
  (`#14819 <https://github.com/coq/coq/pull/14819>`_,
  by Pierre Roux).
