- **Added:**
  Let the user specify a scope for abbreviation arguments, e.g.
  ``Notation abbr X := t (X in scope my_scope)``.
  (`#13965 <https://github.com/coq/coq/pull/13965>`_,
  by Enrico Tassi).
- **Changed:**
  The error ``Argument X was previously inferred to be in scope
  XXX_scope but is here used in YYY_scope.`` is now the warning
  ``[inconsistent-scopes,syntax]`` and can be silenced by
  specifying the scope of the argument
  (`#13965 <https://github.com/coq/coq/pull/13965>`_,
  by Enrico Tassi).
