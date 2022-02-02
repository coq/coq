- **Changed:**
  :tacn:`rewrite` when used to rewrite in multiple hypotheses (eg `rewrite foo in H,H'`) requires that the term (`foo`) does not depend on the hypotheses it rewrites.
  When using `rewrite in *`, this means we only rewrite in hypotheses which do not appear in the term.
  (`#15426 <https://github.com/coq/coq/pull/15426>`_,
  fixes `#3051 <https://github.com/coq/coq/issues/3051>`_
  and `#15448 <https://github.com/coq/coq/issues/15448>`_,
  by Gaëtan Gilbert).
