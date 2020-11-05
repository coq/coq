- **Deprecated**
  ``Numeral.v`` is deprecated, please use ``Number.v`` instead.
- **Changed**
  Rational and real constants are parsed differently.
  The exponent is now encoded separately from the fractional part
  using ``Z.pow_pos``. This way, parsing large exponents can no longer
  blow up and constants are printed in a form closer to the one they
  were parsed (i.e., ``102e-2`` is reprinted as such and not ``1.02``).
- **Removed**
  OCaml parser and printer for real constants have been removed.
  Real constants are now handled with proven Coq code.
- **Added:**
  :ref:`Number Notation <number-notations>` and :ref:`String Notation
  <string-notations>` commands now
  support parameterized inductive and non inductive types
  (`#12218 <https://github.com/coq/coq/pull/12218>`_,
  fixes `#12035 <https://github.com/coq/coq/issues/12035>`_,
  by Pierre Roux, review by Jason Gross and Jim Fehrle for the
  reference manual).
