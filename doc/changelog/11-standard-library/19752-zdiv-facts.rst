- **Added:** lemmas about :g:`Z.modulo`, some in a new module :g:`Zdiv_facts`.
  On its own, :g:`Z.mod_id_iff` generalizes :g:`Z.mod_small`, whereas
  :g:`Z.diveq_iff` and :g:`Z.mod_diveq_iff` further genralize the same concept
  to known quotients other than 0. Combinations of :g:`Z.modulo` with
  :g:`Z.opp` or :g:`Z.abs` are the subject of
  :g:`Z.mod_opp_mod_opp`,
  :g:`Z.mod_mod_opp_r`,
  :g:`Z.mod_opp_r_mod`,
  :g:`Z.mod_mod_abs_r`,
  :g:`Z.mod_abs_r_mod`,
  :g:`Z.eq_mod_opp`,
  :g:`Z.eq_mod_abs`.
  Lemmas :g:`cong_iff_0` and :g:`cong_iff_ex` can be used to reduce congruence
  equalities to equations where only one side is headed by :g:`Z.modulo`.
  Lemmas :g:`Z.gcd_mod_l` and :g:`Z.gcd_mod_r` generalize :g:`Z.gcd_mod`.
  Lemma :g:`Z.mod_mod_divide` generalizes :g:`Zmod_mod`.
  Lemma :g:`Z.mod_pow_l` allows pushing modulo inside exponentiation
  (`#19752 <https://github.com/coq/coq/pull/19752>`_,
  by Andres Erbsen).
