- **Changed:**
  The definition of ``Nat.gcd`` now uses immediate structural recursion,
  without traversing subterm analysis. Its successor equation is available
  as ``Nat.gcd_S`` instead of holding by conversion; proofs that relied on
  unfolding should rewrite with this lemma. The helper invariant
  ``Nat.gcd0_spec`` and zero equation ``Nat.gcd_0`` are also provided
  (`#22579 <https://github.com/rocq-prover/rocq/pull/22579>`_,
  by Thomas Lamiaux).
