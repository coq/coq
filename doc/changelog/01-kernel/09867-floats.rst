- A built-in support of floating-point arithmetic was added, allowing
  one to devise efficient reflection tactics involving numerical
  computation. Primitive floats are added in the language of terms,
  following the binary64 format of the IEEE 754 standard, and the
  related operations are implemented for the different reduction
  engines of Coq by using the corresponding processor operators in
  rounding-to-nearest-even. The properties of these operators are
  axiomatized in the theory :g:`Coq.Floats.FloatAxioms` which is part
  of the library :g:`Coq.Floats.Floats`.
  See Section :ref:`primitive-floats`
  (`#9867 <https://github.com/coq/coq/pull/9867>`_,
  closes `#8276 <https://github.com/coq/coq/issues/8276>`_,
  by Guillaume Bertholon, Erik Martin-Dorel, Pierre Roux).
