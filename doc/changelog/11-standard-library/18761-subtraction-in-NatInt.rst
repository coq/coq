-- **Added:**
   functor types :g:`IsNatInt`, :g:`NatIntOrderProp`, :g:`NatIntAddOrderProp`

   lemmas :g:`sub_succ`,
   :g:`add_add_simpl_l_l`,
   :g:`add_add_simpl_l_r`,
   :g:`add_add_simpl_r_l`,
   :g:`add_add_simpl_r_r`,
   :g:`add_simpl_l`,
   :g:`add_simpl_r`,
   :g:`le_lt_sub_lt`,
   :g:`lt_0_sub`,
   :g:`lt_exists_sub`
   :g:`mul_pred_l`,
   :g:`add_sub_eq_l`,
   :g:`add_sub_eq_r`,
   :g:`add_sub`,
   :g:`add_simpl_l`,
   :g:`sub_add_distr`,
   :g:`le_sub_le_add_r`,
   :g:`le_sub_le_add_l`,
   :g:`lt_add_lt_sub_r`,
   :g:`lt_add_lt_sub_l`,
   :g:`le_lt_sub_lt`,
   :g:`mul_pred_r`,
   :g:`mul_pred_l`,
   :g:`mul_sub_distr_r`,
   :g:`mul_sub_distr_l` in :g:`NatIntOrderProp` which is
   included in :g:`Zbase` and :g:`NBase`. As a result, any of these
   lemmas is now included in :g:`BinInt`, :g:`BinNat` and :g:`PeanoNat`

-- **Removed:**
   functor types :g:`NZAxiomsSig` and :g:`NZAxiomsSig'` which were
   aliases for :g:`NZBasicFunsSig` and :g:`NZBasicFunsSig'`

-- **Changed:**
   the order of the parameters in :g:`mul_sub_distr_l` in :g:`PeanoNat` and :g:`BinNat`, for consistency; the parameters are now the same
   as in `BinInt`. One can recover the previous order with
   `fun n m p => mul_sub_distr_l p n m`

(`#18761 <https://github.com/coq/coq/pull/18761>`_,
by Pierre Rousselin).
