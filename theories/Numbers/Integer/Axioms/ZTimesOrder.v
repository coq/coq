Require Export ZTimes.
Require Export ZPlusOrder.

Module ZTimesOrderProperties (Import ZTimesModule : ZTimesSignature)
                             (Import ZOrderModule : ZOrderSignature with
                               Module ZBaseMod := ZTimesModule.ZPlusModule.ZBaseMod).
Module Export ZTimesPropertiesModule := ZTimesProperties ZTimesModule.
Module Export ZPlusOrderPropertiesModule :=
  ZPlusOrderProperties ZTimesModule.ZPlusModule ZOrderModule.
Open Local Scope IntScope.

Theorem mult_lt_compat_r : forall n m p, 0 < p -> n < m -> n * p < m * p.
Proof.
intros n m p; induct_ord p.
intros H _; false_hyp H lt_irr.
intros p H IH H1 H2. do 2 rewrite times_succ.
apply -> lt_succ in H1; Zle_elim H1.
apply plus_lt_compat. now apply IH. assumption.
rewrite <- H1. do 2 rewrite times_0; now do 2 rewrite plus_0.
intros p H IH H1 H2. apply lt_n_predm in H1. apply -> le_gt in H.
false_hyp H1 H.
Qed.

Theorem mult_lt_compat_l : forall n m p, 0 < p -> n < m -> p * n < p * m.
Proof.
intros n m p. rewrite (times_comm p n); rewrite (times_comm p m).
apply mult_lt_compat_r.
Qed.

Theorem mult_lt_le_compat_r : forall n m p, 0 < p -> n <= m -> n * p <= m * p.
Proof.
intros n m p H1 H2; Zle_elim H2.
Zle_intro1; now apply mult_lt_compat_r.
rewrite H2. now Zle_intro2.
Qed.

Theorem mult_lt_le_compat_l : forall n m p, 0 < p -> n <= m -> p * n <= p * m.
Proof.
intros n m p. rewrite (times_comm p n); rewrite (times_comm p m).
apply mult_lt_le_compat_r.
Qed.

(* And so on *)

Theorem mult_pos_pos : forall n m, 0 < n -> 0 < m -> 0 < n * m.
Proof.
intros n m; set (k := 0) in |-* at 3;
setoid_replace k with (n * 0); unfold k; clear k.
apply mult_lt_compat_l. now rewrite times_0.
Qed.

Theorem mult_pos_neg : forall n m, 0 < n -> m < 0 -> n * m < 0.
Proof.
intros n m; set (k := 0) in |-* at 3;
setoid_replace k with (n * 0); unfold k; clear k.
apply mult_lt_compat_l. now rewrite times_0.
Qed.
(* The same proof script as for mult_pos_pos! *)

Theorem mult_neg_pos : forall n m, n < 0 -> 0 < m -> n * m < 0.
Proof.
intros n m H1 H2; rewrite times_comm; now apply mult_pos_neg.
Qed.

Theorem mult_neg_neg : forall n m, n < 0 -> m < 0 -> 0 < n * m.
Proof.
intros n m H1 H2. setoid_replace (n * m) with (- - (n * m));
[| symmetry; apply double_opp].
rewrite <- times_opp_l. rewrite <- times_opp_r.
apply -> lt_opp_neg in H1. apply -> lt_opp_neg in H2.
now apply mult_pos_pos.
Qed.

(** With order, Z is an integral domain *)
Theorem mult_neq_0 : forall n m, n # 0 -> m # 0 -> n * m # 0.
Proof.
intros n m H1 H2.
destruct (lt_total n 0) as [H3 | [H3 | H3]];
destruct (lt_total m 0) as [H4 | [H4 | H4]].
apply neq_symm. apply lt_neq. now apply mult_neg_neg.
false_hyp H4 H2.
apply lt_neq; now apply mult_neg_pos.
false_hyp H3 H1. false_hyp H3 H1. false_hyp H3 H1.
apply lt_neq; now apply mult_pos_neg.
false_hyp H4 H2.
apply neq_symm. apply lt_neq. now apply mult_pos_pos.
Qed.

End ZTimesOrderProperties.


(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
