- **Changed**
  Moved 39 lemmas and notations about the rationals `Q` from the constructive reals private file `theories/Reals/Cauchy/QExtra.v` to appropriate files in `theories/QArith`.
  The now public lemmas are mostly about compatibility of multiplication and power with relational operators and simple convenience lemmas e.g. for reduction of `Q` values.
  The following moved lemmas have been renamed:
  `Q_factorDenom` to `Qmult_frac_l`,
  `Q_reduce_fl` to `Qreduce_num_l`,
  `Qle_neq` to `Qlt_leneq`,
  `Qmult_lt_le_compat_nonneg` to `Qmult_le_lt_compat_pos`,
  `Qpower_pos_lt` to `Qpower_0_lt`,
  `Qpower_lt_1_increasing` to `Qpower_1_lt_pos`,
  `Qpower_lt_1_increasing'` to `Qpower_1_lt`,
  `Qpower_le_1_increasing` to `Qpower_1_le_pos`,
  `Qpower_le_1_increasing'` to `Qpower_1_le`,
  `Qzero_eq` to `Qreduce_zero`,
  `Qpower_lt_compat` to `Qpower_lt_compat_l`,
  `Qpower_le_compat` to `Qpower_le_compat_l`,
  `Qpower_lt_compat_inv` to `Qpower_lt_compat_l_inv`,
  `Qpower_le_compat_inv` to `Qpower_le_compat_l_inv`,
  `Qpower_decomp'` to `Qpower_decomp_pos` and
  `QarchimedeanExp2_Pos` to `Qarchimedean_power2_pos`.
  The following lemmas have been renamed and the sides of the equality swapped:
  `Qinv_swap_pos` to `Qinv_pos`,
  `Qinv_swap_neg` to `Qinv_neg` and.
  The following lemmas have been deleted:
  `Q_factorNum_l` and `Q_factorNum`.
  The lemma `Qopp_lt_compat` has been moved from `theories/QArith/Qround.v` to `theories/QArith/QArith_base.v`.
  About 10 additional lemmas have been added for similar cases as the moved lemmas.
  Compatibility notations are not provided because QExtra is considered internal (excluded from the library documentation).
  (`#14293 <https://github.com/coq/coq/pull/14293>`_,
  by Michael Soegtrop).
