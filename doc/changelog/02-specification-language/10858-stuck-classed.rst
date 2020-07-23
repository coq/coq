- **Changed:**
  Typeclass resolution, accessible through :tacn:`typeclasses eauto`,
  now suspends constraints according to their modes
  instead of failing. If a typeclass constraint does not match
  any of the declared modes for its class, the constraint is postponed, and
  the proof search continues on other goals. Proof search does a fixed point
  computation to try to solve them at a later stage of resolution. It does
  not fail if there remain only stuck constraints at the end of resolution.
  This makes typeclasses with declared modes more robust with respect to the
  order of resolution.
  (`#10858 <https://github.com/coq/coq/pull/10858>`_,
  fixes `#9058 <https://github.com/coq/coq/issues/9058>_`, by Matthieu Sozeau).
