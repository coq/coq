- **Fixed:**
  `roqchk --output-context` did not report axioms used through inductives sealed in a module
  (such that a file exposing a constant of type `False` could still report "no axioms").
  The fix also changes how axioms declared inside a functor are reported (they are reported using the name inside the functor instead of reporting each result of applying the functor)
  and causes unused axioms in a sealed module to be reported where they previously were not reported
  (`#22623 <https://github.com/rocq-prover/rocq/pull/22623>`_,
  fixes `#22618 <https://github.com/rocq-prover/rocq/issues/22618>`_,
  by Gaëtan Gilbert).
