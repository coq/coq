(* This failed in 8.3pl2 *)

Scheme Induction for eq Sort Prop.
Check eq_ind_dep.

(* This was broken in v8.5 *)

Set Rewriting Schemes.
Inductive myeq A (a:A) : A -> Prop := myrefl : myeq A a a.
Unset Rewriting Schemes.

Check myeq_rect.
Check myeq_ind.
Check myeq_rec.
Check myeq_congr.
Check myeq_sym_internal.
Check myeq_rew.
Check myeq_rew_dep.
Check myeq_rew_fwd_dep.
Check myeq_rew_r.
Check internal_myeq_sym_involutive.
Check myeq_rew_r_dep.
Check myeq_rew_fwd_r_dep.

Set Rewriting Schemes.
Inductive myeq_true : bool -> Prop := myrefl_true : myeq_true true.
Unset Rewriting Schemes.
