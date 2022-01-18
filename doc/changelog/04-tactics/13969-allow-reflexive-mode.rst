- **Changed:**
  The ``RewriteRelation`` type class is now used to declare relations
  inferrable by the :tacn:`setoid_rewrite` tactic to construct
  ``Proper`` instances. This can break developments that relied on
  existing ``Reflexive`` instances to infer relations. The fix is
  to simply add a (backwards compatible) ``RewriteRelation`` declaration
  for the relation. This change allows to set stricter modes on the
  relation type classes ``Reflexive``, ``Symmetric``, etc.
  (`#13969 <https://github.com/coq/coq/pull/13969>`_,
  fixes `#7916 <https://github.com/coq/coq/issues/7916>`_,
  by Matthieu Sozeau).
