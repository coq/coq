- **Added:**
  flags ``Printing Reversible Up To Unification``,
  ``Printing Reversible Up To Conversion Modulo Sorts And Universes``,
  ``Printing Reversible Up To Conversion Modulo Universes``,
  ``Printing Reversible Up To Conversion Modulo Universe Unification`` and
  ``Printing Reversible Up To Conversion``, which check, each time a term
  is printed, that the printed form can be parsed and elaborated back to
  a term equal to the original one up to the selected equivalence, and
  progressively turn more printing options on until this is the case
  (`#22283 <https://github.com/rocq-prover/rocq/pull/22283>`_,
  written by Claude (Anthropic), for Jason Gross).
