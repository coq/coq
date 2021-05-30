- **Changed:**
  The hints mode ``!`` matches a term iff the applicative head is not an existential variable.
  It now also matches projections applied to any term or a `match` on any term.
  (`#14392 <https://github.com/coq/coq/pull/14392>`_,
  by Matthieu Sozeau).
