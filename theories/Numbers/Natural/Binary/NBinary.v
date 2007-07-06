Require Import NArith.
Require Import Ndec.

Require Export NDepRec.
Require Export NTimesLt.
Require Export NMiscFunct.

Open Local Scope N_scope.

Module BinaryDomain : DomainEqSignature
  with Definition N := N
  with Definition E := (@eq N)
  with Definition e := Neqb.

Definition N := N.
Definition E := (@eq N).
Definition e := Neqb.

Theorem E_equiv_e : forall x y : N, E x y <-> e x y.
Proof.
unfold E, e; intros x y; split; intro H;
[rewrite H; now rewrite Neqb_correct |
apply Neqb_complete; now inversion H].
Qed.

Definition E_equiv : equiv N E := eq_equiv N.

Add Relation N E
 reflexivity proved by (proj1 E_equiv)
 symmetry proved by (proj2 (proj2 E_equiv))
 transitivity proved by (proj1 (proj2 E_equiv))
as E_rel.

End BinaryDomain.

Module BinaryNat <: NatSignature.

Module Export DomainModule := BinaryDomain.

Definition O := N0.
Definition S := Nsucc.

Add Morphism S with signature E ==> E as S_wd.
Proof.
congruence.
Qed.

Theorem induction :
  forall P : N -> Prop, pred_wd E P ->
    P 0 -> (forall n, P n -> P (S n)) -> forall n, P n.
Proof.
intros P P_wd; apply Nind.
Qed.

Definition recursion (A : Set) (a : A) (f : N -> A -> A) (n : N) :=
  Nrec (fun _ => A) a f n.
Implicit Arguments recursion [A].

Theorem recursion_wd :
forall (A : Set) (EA : relation A),
  forall a a' : A, EA a a' ->
    forall f f' : N -> A -> A, eq_fun2 E EA EA f f' ->
      forall x x' : N, x = x' ->
        EA (recursion a f x) (recursion a' f' x').
Proof.
unfold fun2_wd, E, eq_fun2.
intros A EA a a' Eaa' f f' Eff'.
intro x; pattern x; apply Nind.
intros x' H; now rewrite <- H.
clear x.
intros x IH x' H; rewrite <- H.
unfold recursion, Nrec in *; do 2 rewrite Nrect_step.
now apply Eff'; [| apply IH].
Qed.

Theorem recursion_0 :
  forall (A : Set) (a : A) (f : N -> A -> A), recursion a f 0 = a.
Proof.
intros A a f; unfold recursion; unfold Nrec; now rewrite Nrect_base.
Qed.

Theorem recursion_S :
  forall (A : Set) (EA : relation A) (a : A) (f : N -> A -> A),
    EA a a -> fun2_wd E EA EA f ->
      forall n : N, EA (recursion a f (S n)) (f n (recursion a f n)).
Proof.
unfold E, recursion, Nrec, fun2_wd; intros A EA a f EAaa f_wd n; pattern n; apply Nind.
rewrite Nrect_step; rewrite Nrect_base; now apply f_wd.
clear n; intro n; do 2 rewrite Nrect_step; intro IH. apply f_wd; [reflexivity|].
now rewrite Nrect_step.
Qed.

End BinaryNat.

Module BinaryDepRec <: DepRecSignature.
Module Export DomainModule := BinaryDomain.
Module Export NatModule := BinaryNat.

Definition dep_recursion := Nrec.

Theorem dep_recursion_0 :
  forall (A : N -> Set) (a : A 0) (f : forall n, A n -> A (S n)),
    dep_recursion A a f 0 = a.
Proof.
intros A a f; unfold dep_recursion; unfold Nrec; now rewrite Nrect_base.
Qed.

Theorem dep_recursion_S :
  forall (A : N -> Set) (a : A 0) (f : forall n, A n -> A (S n)) (n : N),
    dep_recursion A a f (S n) = f n (dep_recursion A a f n).
Proof.
intros A a f n; unfold dep_recursion; unfold Nrec; now rewrite Nrect_step.
Qed.

End BinaryDepRec.

Module BinaryPlus <: PlusSignature.

Module Export NatModule := BinaryNat.

Definition plus := Nplus.

Add Morphism plus with signature E ==> E ==> E as plus_wd.
Proof.
unfold E; congruence.
Qed.

Theorem plus_0_n : forall n, 0 + n = n.
Proof.
exact Nplus_0_l.
Qed.

Theorem plus_Sn_m : forall n m, (S n) + m = S (n + m).
Proof.
exact Nplus_succ.
Qed.

End BinaryPlus.

Module BinaryTimes <: TimesSignature.
Module Export PlusModule := BinaryPlus.

Definition times := Nmult.

Add Morphism times with signature E ==> E ==> E as times_wd.
Proof.
unfold E; congruence.
Qed.

Theorem times_0_n : forall n, 0 * n = 0.
Proof.
exact Nmult_0_l.
Qed.

Theorem times_Sn_m : forall n m, (S n) * m = m + n * m.
Proof.
exact Nmult_Sn_m.
Qed.

End BinaryTimes.

Module BinaryLt <: LtSignature.
Module Export NatModule := BinaryNat.

Definition lt (m n : N) := less_than (Ncompare m n).

Add Morphism lt with signature E ==> E ==> eq_bool as lt_wd.
Proof.
unfold E; congruence.
Qed.

Theorem lt_0 : forall x, ~ (lt x 0).
Proof.
unfold lt; destruct x as [|x]; simpl; now intro.
Qed.

Theorem lt_S : forall x y, lt x (S y) <-> lt x y \/ x = y.
Proof.
intros x y.
assert (H1 : lt x (S y) <-> Ncompare x (S y) = Lt);
[unfold lt, less_than; destruct (x ?= S y); simpl; split; now intro |].
assert (H2 : lt x y <-> Ncompare x y = Lt);
[unfold lt, less_than; destruct (x ?= y); simpl; split; now intro |].
pose proof (Ncompare_n_Sm x y) as H. tauto.
Qed.

End BinaryLt.

Module Export BinaryTimesLtProperties := TimesLtProperties BinaryTimes BinaryLt.

(*Module Export BinaryRecEx := MiscFunctFunctor BinaryNat.*)

(* Just some fun comparing the efficiency of the generic log defined
by strong (course-of-value) recursion and the log defined by recursion
on notation *)
(* Time Eval compute in (log 100000). *) (* 98 sec *)

(*
Fixpoint binposlog (p : positive) : N :=
match p with
| xH => 0
| xO p' => Nsucc (binposlog p')
| xI p' => Nsucc (binposlog p')
end.

Definition binlog (n : N) : N :=
match n with
| 0 => 0
| Npos p => binposlog p
end.
*)
(* Eval compute in (binlog 1000000000000000000). *) (* Works very fast *)
