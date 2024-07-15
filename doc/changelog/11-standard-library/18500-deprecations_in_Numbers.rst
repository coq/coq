- **Deprecated:**
  The library files

  * ``Coq.Numbers.Integer.Binary.ZBinary``
  * ``Coq.Numbers.Integer.NatPairs.ZNatPairs``
  * ``Coq.Numbers.Natural.Binary.NBinary``

  have been deprecated.
  Users should require ``Coq.Arith.PeanoNat`` or ``Coq.Arith.NArith.BinNat``
  if they want implementations of natural numbers and
  ``Coq.Arith.ZArith.BinInt`` if they want an implementation of integers
  (`#18500 <https://github.com/coq/coq/pull/18500>`_,
  by Pierre Rousselin).
