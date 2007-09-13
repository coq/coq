Require Export NumPrelude.
Require Import NZBase.

Module Type NBaseSig.

Parameter Inline N : Set.
Parameter Inline E : N -> N -> Prop.
Parameter Inline O : N.
Parameter Inline S : N -> N.

Delimit Scope NatScope with Nat.
Open Local Scope NatScope.

Notation "x == y" := (E x y) (at level 70) : NatScope.
Notation "x ~= y" := (~ E x y) (at level 70) : NatScope.
Notation "0" := O : NatScope.
Notation "1" := (S O) : NatScope.

Axiom E_equiv : equiv N E.
Add Relation N E
 reflexivity proved by (proj1 E_equiv)
 symmetry proved by (proj2 (proj2 E_equiv))
 transitivity proved by (proj1 (proj2 E_equiv))
as E_rel.

Add Morphism S with signature E ==> E as S_wd.

Axiom succ_inj : forall n1 n2 : N, S n1 == S n2 -> n1 == n2.
Axiom succ_neq_0 : forall n : N, S n ~= 0.

Axiom induction :
  forall A : N -> Prop, predicate_wd E A ->
    A 0 -> (forall n : N, A n -> A (S n)) -> forall n : N, A n.

End NBaseSig.

Module NBasePropFunct (Import NBaseMod : NBaseSig).
Open Local Scope NatScope.

(*Theorem E_equiv : equiv N E.
Proof E_equiv.

Theorem succ_inj_wd : forall n1 n2 : N, S n1 == S n2 <-> n1 == n2.
Proof succ_inj_wd.

Theorem succ_neq_0 : forall n : N, S n ~= 0.
Proof succ_neq_0.

Theorem induction :
  forall A : N -> Prop, predicate_wd E A ->
    A 0 -> (forall n : N, A n -> A (S n)) -> forall n : N, A n.
Proof induction.*)

Module NZBaseMod <: NZBaseSig.
Definition NZ := N.
Definition NZE := E.
Definition NZ0 := 0.
Definition NZsucc := S.

(* Axioms *)
Definition NZE_equiv := E_equiv.
Definition NZsucc_inj := succ_inj.

Add Relation NZ NZE
 reflexivity proved by (proj1 NZE_equiv)
 symmetry proved by (proj2 (proj2 NZE_equiv))
 transitivity proved by (proj1 (proj2 NZE_equiv))
as NZE_rel.

Add Morphism NZsucc with signature NZE ==> NZE as NZsucc_wd.
Proof S_wd.

Theorem NZinduction :
  forall A : N -> Prop, predicate_wd E A ->
    A 0 -> (forall n : N, A n <-> A (S n)) -> forall n : N, A n.
Proof.
intros A A_wd Base Step.
apply induction; try assumption.
intros; now apply -> Step.
Qed.

End NZBaseMod.

Module Export NZBasePropMod := NZBasePropFunct NZBaseMod.

Theorem neq_symm : forall n m : N, n ~= m -> m ~= n.
Proof NZneq_symm.

Theorem succ_inj_wd_neg : forall n m : N, S n ~= S m <-> n ~= m.
Proof NZsucc_inj_wd_neg.

Ltac induct n := induction_maker n ltac:(apply induction).

Theorem nondep_induction :
  forall A : N -> Prop, predicate_wd E A ->
    A 0 -> (forall n : N, A (S n)) -> forall n : N, A n.
Proof.
intros; apply induction; auto.
Qed.

Ltac nondep_induct n := induction_maker n ltac:(apply nondep_induction).

Theorem neq_0 : ~ forall n, n == 0.
Proof.
intro H; apply (succ_neq_0 0). apply H.
Qed.

Theorem neq_0_succ : forall n, n ~= 0 <-> exists m, n == S m.
Proof.
nondep_induct n. split; intro H;
[now elim H | destruct H as [m H]; symmetry in H; false_hyp H succ_neq_0].
intro n; split; intro H; [now exists n | apply succ_neq_0].
Qed.

Theorem zero_or_succ : forall n, n == 0 \/ exists m, n == S m.
Proof.
nondep_induct n; [now left | intros n; right; now exists n].
Qed.

(* The following is useful for reasoning about, e.g., Fibonacci numbers *)
Section DoubleInduction.

Variable A : N -> Prop.
Hypothesis A_wd : predicate_wd E A.

Add Morphism A with signature E ==> iff as A_morph.
Proof.
exact A_wd.
Qed.

Theorem double_induction :
  A 0 -> A 1 ->
    (forall n, A n -> A (S n) -> A (S (S n))) -> forall n, A n.
Proof.
intros until 3.
assert (D : forall n, A n /\ A (S n)); [ |intro n; exact (proj1 (D n))].
induct n; [ | intros n [IH1 IH2]]; auto.
Qed.

End DoubleInduction.

Ltac double_induct n := induction_maker n ltac:(apply double_induction).

(* The following is useful for reasoning about, e.g., Ackermann function *)
Section TwoDimensionalInduction.

Variable R : N -> N -> Prop.
Hypothesis R_wd : rel_wd E E R.

Add Morphism R with signature E ==> E ==> iff as R_morph.
Proof.
exact R_wd.
Qed.

Theorem two_dim_induction :
   R 0 0 ->
   (forall n m, R n m -> R n (S m)) ->
   (forall n, (forall m, R n m) -> R (S n) 0) -> forall n m, R n m.
Proof.
intros H1 H2 H3. induct n.
induct m.
exact H1. exact (H2 0).
intros n IH. induct m.
now apply H3. exact (H2 (S n)).
Qed.

End TwoDimensionalInduction.

Ltac two_dim_induct n m :=
  try intros until n;
  try intros until m;
  pattern n, m; apply two_dim_induction; clear n m;
  [unfold rel_wd; unfold fun2_wd;
   let x1 := fresh "x" in
   let y1 := fresh "y" in
   let H1 := fresh "H" in
   let x2 := fresh "x" in
   let y2 := fresh "y" in
   let H2 := fresh "H" in
     intros x1 y1 H1 x2 y2 H2;
     qsetoid_rewrite H1;
     qiff x2 y2 H2 | | | ].
(* This is not a very efficient approach because qsetoid_rewrite uses
qiff to take the formula apart in order to make it quantifier-free,
and then qiff is called again and takes the formula apart for the
second time. It is better to analyze the formula once and generalize
qiff to take a list of equalities that it has to rewrite. *)

End NBasePropFunct.


(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
