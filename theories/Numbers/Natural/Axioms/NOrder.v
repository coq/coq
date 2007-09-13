Require Export NBase.
Require Import NZOrder.

Module Type NOrderSig.
Declare Module Export NBaseMod : NBaseSig.
Open Local Scope NatScope.

Parameter Inline lt : N -> N -> Prop.
Parameter Inline le : N -> N -> Prop.

Notation "x < y" := (lt x y) : NatScope.
Notation "x <= y" := (le x y) : NatScope.
Notation "x > y" := (lt y x) (only parsing) : NatScope.
Notation "x >= y" := (le y x) (only parsing) : NatScope.

Add Morphism lt with signature E ==> E ==> iff as lt_wd.
Add Morphism le with signature E ==> E ==> iff as le_wd.

Axiom le_lt_or_eq : forall x y, x <= y <-> x < y \/ x == y.
Axiom nlt_0_r : forall x, ~ (x < 0).
Axiom lt_succ_le : forall x y, x < S y <-> x <= y.

End NOrderSig.

Module NOrderPropFunct (Import NOrderModule : NOrderSig).
Module Export NBasePropMod := NBasePropFunct NBaseMod.
Open Local Scope NatScope.

Ltac le_intro1 := rewrite le_lt_or_eq; left.
Ltac le_intro2 := rewrite le_lt_or_eq; right.
Ltac le_elim H := rewrite le_lt_or_eq in H; destruct H as [H | H].

Theorem lt_succ_lt : forall n m : N, S n < m -> n < m.
Proof.
intro n; induct m.
intro H; false_hyp H nlt_0_r.
intros m IH H. apply <- lt_succ_le. apply -> lt_succ_le in H. le_elim H.
le_intro1; now apply IH.
rewrite <- H; le_intro1. apply <- lt_succ_le; now le_intro2.
Qed.

Theorem lt_irrefl : forall n : N, ~ (n < n).
Proof.
induct n.
apply nlt_0_r.
intros n IH H. apply -> lt_succ_le in H; le_elim H.
apply lt_succ_lt in H; now apply IH.
assert (n < S n) by (apply <- lt_succ_le; now le_intro2).
rewrite H in *; now apply IH.
Qed.

Module NZOrderMod <: NZOrderSig.
Module NZBaseMod := NZBaseMod.

Definition NZlt := lt.
Definition NZle := le.

Add Morphism NZlt with signature E ==> E ==> iff as NZlt_wd.
Proof lt_wd.

Add Morphism NZle with signature E ==> E ==> iff as NZle_wd.
Proof le_wd.

Definition NZle_lt_or_eq := le_lt_or_eq.
Definition NZlt_succ_le := lt_succ_le.
Definition NZlt_succ_lt := lt_succ_lt.
Definition NZlt_irrefl := lt_irrefl.

End NZOrderMod.

Module Export NZOrderPropMod := NZOrderPropFunct NZOrderMod.

(* Renaming theorems from NZOrder.v *)

Theorem lt_le_incl : forall n m : N, n < m -> n <= m.
Proof NZlt_le_incl.

Theorem lt_neq : forall n m : N, n < m -> n ~= m.
Proof NZlt_neq.

Theorem le_refl : forall n : N, n <= n.
Proof NZle_refl.

Theorem lt_succ_r : forall n : N, n < S n.
Proof NZlt_succ_r.

Theorem le_succ_r : forall n : N, n <= S n.
Proof NZle_succ_r.

Theorem lt_lt_succ : forall n m : N, n < m -> n < S m.
Proof NZlt_lt_succ.

Theorem le_le_succ : forall n m : N, n <= m -> n <= S m.
Proof NZle_le_succ.

Theorem le_succ_le_or_eq_succ : forall n m : N, n <= S m <-> n <= m \/ n == S m.
Proof NZle_succ_le_or_eq_succ.

Theorem neq_succ_l : forall n : N, S n ~= n.
Proof NZneq_succ_l.

Theorem nlt_succ_l : forall n : N, ~ S n < n.
Proof NZnlt_succ_l.

Theorem nle_succ_l : forall n : N, ~ S n <= n.
Proof NZnle_succ_l.

Theorem lt_le_succ : forall n m : N, n < m <-> S n <= m.
Proof NZlt_le_succ.

Theorem le_succ_le : forall n m : N, S n <= m -> n <= m.
Proof NZle_succ_le.

Theorem succ_lt_mono : forall n m : N, n < m <-> S n < S m.
Proof NZsucc_lt_mono.

Theorem succ_le_mono : forall n m : N, n <= m <-> S n <= S m.
Proof NZsucc_le_mono.

Theorem lt_lt_false : forall n m, n < m -> m < n -> False.
Proof NZlt_lt_false.

Theorem lt_asymm : forall n m, n < m -> ~ m < n.
Proof NZlt_asymm.

Theorem lt_trans : forall n m p : N, n < m -> m < p -> n < p.
Proof NZlt_trans.

Theorem le_trans : forall n m p : N, n <= m -> m <= p -> n <= p.
Proof NZle_trans.

Theorem le_lt_trans : forall n m p : N, n <= m -> m < p -> n < p.
Proof NZle_lt_trans.

Theorem lt_le_trans : forall n m p : N, n < m -> m <= p -> n < p.
Proof NZlt_le_trans.

Theorem le_antisymm : forall n m : N, n <= m -> m <= n -> n == m.
Proof NZle_antisymm.

(** Trichotomy, decidability, and double negation elimination *)

Theorem lt_trichotomy : forall n m : N,  n < m \/ n == m \/ m < n.
Proof NZlt_trichotomy.

Theorem le_lt_dec : forall n m : N, n <= m \/ m < n.
Proof NZle_lt_dec.

Theorem le_nlt : forall n m : N, n <= m <-> ~ m < n.
Proof NZle_nlt.

Theorem lt_dec : forall n m : N, n < m \/ ~ n < m.
Proof NZlt_dec.

Theorem lt_dne : forall n m, ~ ~ n < m <-> n < m.
Proof NZlt_dne.

Theorem nle_lt : forall n m : N, ~ n <= m <-> m < n.
Proof NZnle_lt.

Theorem le_dec : forall n m : N, n <= m \/ ~ n <= m.
Proof NZle_dec.

Theorem le_dne : forall n m : N, ~ ~ n <= m <-> n <= m.
Proof NZle_dne.

Theorem lt_nlt_succ : forall n m : N, n < m <-> ~ m < S n.
Proof NZlt_nlt_succ.

Theorem lt_exists_pred :
  forall z n : N, z < n -> exists k : N, n == S k /\ z <= k.
Proof NZlt_exists_pred.

Theorem lt_succ_iter_r :
  forall (n : nat) (m : N), m < NZsucc_iter (Datatypes.S n) m.
Proof NZlt_succ_iter_r.

Theorem neq_succ_iter_l :
  forall (n : nat) (m : N), NZsucc_iter (Datatypes.S n) m ~= m.
Proof NZneq_succ_iter_l.

(** Stronger variant of induction with assumptions n >= 0 (n < 0)
in the induction step *)

Theorem right_induction :
  forall A : N -> Prop, predicate_wd E A ->
    forall z : N, A z ->
      (forall n : N, z <= n -> A n -> A (S n)) ->
        forall n : N, z <= n -> A n.
Proof NZright_induction.

Theorem left_induction :
  forall A : N -> Prop, predicate_wd E A ->
    forall z : N, A z ->
      (forall n : N, n < z -> A (S n) -> A n) ->
        forall n : N, n <= z -> A n.
Proof NZleft_induction.

Theorem central_induction :
  forall A : N -> Prop, predicate_wd E A ->
    forall z : N, A z ->
      (forall n : N, z <= n -> A n -> A (S n)) ->
      (forall n : N, n < z  -> A (S n) -> A n) ->
        forall n : N, A n.
Proof NZcentral_induction.

Theorem right_induction' :
  forall A : N -> Prop, predicate_wd E A ->
    forall z : N,
      (forall n : N, n <= z -> A n) ->
      (forall n : N, z <= n -> A n -> A (S n)) ->
        forall n : N, A n.
Proof NZright_induction'.

Theorem strong_right_induction' :
  forall A : N -> Prop, predicate_wd E A ->
    forall z : N,
      (forall n : N, n <= z -> A n) ->
      (forall n : N, z <= n -> (forall m : N, z <= m -> m < n -> A m) -> A n) ->
        forall n : N, A n.
Proof NZstrong_right_induction'.

(** Elimintation principle for < *)

Theorem lt_ind :
  forall A : N -> Prop, predicate_wd E A ->
    forall n : N,
      A (S n) ->
      (forall m : N, n < m -> A m -> A (S m)) ->
        forall m : N, n < m -> A m.
Proof NZlt_ind.

(** Elimintation principle for <= *)

Theorem le_ind :
  forall A : N -> Prop, predicate_wd E A ->
    forall n : N,
      A n ->
      (forall m : N, n <= m -> A m -> A (S m)) ->
        forall m : N, n <= m -> A m.
Proof NZle_ind.

(** Theorems that are true for natural numbers but not for integers *)

Theorem le_0_l : forall n : N, 0 <= n.
Proof.
induct n.
now le_intro2.
intros; now apply le_le_succ.
Qed.

Theorem nle_succ_0 : forall n, ~ (S n <= 0).
Proof.
intros n H; apply <- lt_le_succ in H; false_hyp H nlt_0_r.
Qed.

Theorem le_0_eq_0 : forall n, n <= 0 -> n == 0.
Proof.
intros n H; le_elim H; [false_hyp H nlt_0_r | assumption].
Qed.

Theorem lt_0_succ : forall n, 0 < S n.
Proof.
induct n; [apply lt_succ_r | intros n H; now apply lt_lt_succ].
Qed.

Theorem lt_lt_0 : forall n m, n < m -> 0 < m.
Proof.
intros n m; induct n.
trivial.
intros n IH H. apply IH; now apply lt_succ_lt.
Qed.

Theorem neq_0_lt_0 : forall n, 0 ~= n -> 0 < n.
Proof.
nondep_induct n. intro H; now elim H. intros; apply lt_0_succ.
Qed.

Lemma Acc_nonneg_lt : forall n : N,
  Acc (fun n m => 0 <= n /\ n < m) n -> Acc lt n.
Proof.
intros n H; induction H as [n _ H2];
constructor; intros y H; apply H2; split; [apply le_0_l | assumption].
Qed.

Theorem lt_wf : well_founded lt.
Proof.
unfold well_founded; intro n; apply Acc_nonneg_lt. apply NZlt_wf.
Qed.

(** Elimination principlies for < and <= for relations *)

Section RelElim.

(* FIXME: Variable R : relation N. -- does not work *)

Variable R : N -> N -> Prop.
Hypothesis R_wd : rel_wd E E R.

Add Morphism R with signature E ==> E ==> iff as R_morph2.
Proof R_wd.

Theorem le_ind_rel :
   (forall m, R 0 m) ->
   (forall n m, n <= m -> R n m -> R (S n) (S m)) ->
     forall n m, n <= m -> R n m.
Proof.
intros Base Step; induct n.
intros; apply Base.
intros n IH m H. elim H using le_ind.
solve_predicate_wd.
apply Step; [| apply IH]; now le_intro2.
intros k H1 H2. apply le_succ_le in H1. auto.
Qed.

Theorem lt_ind_rel :
   (forall m, R 0 (S m)) ->
   (forall n m, n < m -> R n m -> R (S n) (S m)) ->
   forall n m, n < m -> R n m.
Proof.
intros Base Step; induct n.
intros m H. apply lt_exists_pred in H; destruct H as [m' [H _]].
rewrite H; apply Base.
intros n IH m H. elim H using lt_ind.
solve_predicate_wd.
apply Step; [| apply IH]; now apply lt_succ_r.
intros k H1 H2. apply lt_succ_lt in H1. auto.
Qed.

End RelElim.

End NOrderPropFunct.


(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
