- **Added:**
  modules :g:`Nat.Div0` and :g:`Nat.Lcm0` in :g:`PeanoNat`, and :g:`N.Div0` and :g:`N.Lcm0` in :g:`BinNat`
  containing lemmas regarding :g:`div` and :g:`mod`, which take into account `n div 0 = 0` and `n mod 0 = n`.
  Strictly weaker lemmas are deprecated, and will be removed in the future.
  After the weaker lemmas are removed, the modules :g:`Div0` and :g:`Lcm0` will be deprecated,
  and their contents included directly into :g:`Nat` and :g:`N`.
  Locally, you can use :g:`Module Nat := Nat.Div0.` or :g:`Module Nat := Nat.Lcm0.` to approximate this inclusion
  (`#16203 <https://github.com/coq/coq/pull/16203>`_,
  fixes `#16186 <https://github.com/coq/coq/issues/16186>`_,
  by Andrej Dudenhefner).
- **Added:**
  lemma :g:`measure_induction` in :g:`Nat` and :g:`N` analogous to :g:`Wf_nat.induction_ltof1`,
  which is compatible with the `using` clause for the :tacn:`induction` tactic
  (`#16203 <https://github.com/coq/coq/pull/16203>`_,
  by Andrej Dudenhefner).
- **Removed:**
  from :g:`Nat` and :g:`N` superfluous lemmas :g:`rs_rs'`, :g:`rs'_rs''`, :g:`rbase`, :g:`A'A_right`,
  :g:`ls_ls'`, :g:`ls'_ls''`, :g:`rs'_rs''`, :g:`lbase`, :g:`A'A_left`, and also
  redundant non-negativity assumptions in :g:`gcd_unique`, :g:`gcd_unique_alt`,
  :g:`divide_gcd_iff`, and :g:`gcd_mul_diag_l`
  (`#16203 <https://github.com/coq/coq/pull/16203>`_,
  by Andrej Dudenhefner).
