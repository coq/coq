- **Fixed:**
  ``rocq dep`` no longer treats a ``. `` inside a string literal as the end of
  a sentence, so a ``Require`` written inside a string is no longer recorded as
  a dependency and no longer causes a spurious syntax error
  (`#22443 <https://github.com/rocq-prover/rocq/pull/22443>`_,
  fixes `#22442 <https://github.com/rocq-prover/rocq/issues/22442>`_,
  by Jason Gross).
