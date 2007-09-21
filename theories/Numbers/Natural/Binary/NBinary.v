Require Import NArith.
Require Import NMinus.

Module NBinaryAxiomsMod <: NAxiomsSig.

Open Local Scope N_scope.

Definition N := N.
Definition E := (@eq N).
Definition O := 0.
Definition S := Nsucc.

(*Definition Npred (n : N) := match n with
| 0 => 0
| Npos p => match p with
  | xH => 0
  | _ => Npos (Ppred p)
  end
end.*)

Definition P := Npred.
Definition plus := Nplus.
Definition minus := Nminus.

(*Definition minus (n m : N) :=
match n, m with
| N0, _ => N0
| n, N0 => n
| Npos n', Npos m' =>
  match Pminus_mask n' m' with
  | IsPos p => Npos p
  | _ => N0
  end
end.*)

Definition times := Nmult.
Definition lt := Nlt.
Definition le := Nle.

Theorem E_equiv : equiv N E.
Proof (eq_equiv N).

Add Relation N E
 reflexivity proved by (proj1 E_equiv)
 symmetry proved by (proj2 (proj2 E_equiv))
 transitivity proved by (proj1 (proj2 E_equiv))
as E_rel.

Add Morphism S with signature E ==> E as succ_wd.
Proof.
congruence.
Qed.

Add Morphism P with signature E ==> E as pred_wd.
Proof.
congruence.
Qed.

Add Morphism plus with signature E ==> E ==> E as plus_wd.
Proof.
congruence.
Qed.

Add Morphism minus with signature E ==> E ==> E as minus_wd.
Proof.
congruence.
Qed.

Add Morphism times with signature E ==> E ==> E as times_wd.
Proof.
congruence.
Qed.

Add Morphism lt with signature E ==> E ==> iff as lt_wd.
Proof.
unfold E; intros x1 x2 H1 y1 y2 H2; rewrite H1; now rewrite H2.
Qed.

Add Morphism le with signature E ==> E ==> iff as le_wd.
Proof.
unfold E; intros x1 x2 H1 y1 y2 H2; rewrite H1; now rewrite H2.
Qed.

Theorem induction :
  forall A : N -> Prop, predicate_wd E A ->
    A 0 -> (forall n, A n -> A (Nsucc n)) -> forall n, A n.
Proof.
intros A predicate_wd; apply Nind.
Qed.

Theorem pred_0 : Npred 0 = 0.
Proof.
reflexivity.
Qed.

Theorem pred_succ : forall n : N, Npred (Nsucc n) = n.
Proof.
destruct n as [| p]; simpl. reflexivity.
case_eq (Psucc p); try (intros q H; rewrite <- H; now rewrite Ppred_succ).
intro H; false_hyp H Psucc_not_one.
Qed.

Theorem plus_0_l : forall n : N, 0 + n = n.
Proof Nplus_0_l.

Theorem plus_succ_l : forall n m : N, (Nsucc n) + m = Nsucc (n + m).
Proof Nplus_succ.

Theorem minus_0_r : forall n : N, n - 0 = n.
Proof Nminus_0_r.

Theorem minus_succ_r : forall n m : N, n - (S m) = P (n - m).
Proof Nminus_succ_r.

Theorem times_0_r : forall n : N, n * 0 = 0.
Proof.
intro n; rewrite Nmult_comm; apply Nmult_0_l.
Qed.

Theorem times_succ_r : forall n m : N, n * (Nsucc m) = n * m + n.
Proof.
intros n m; rewrite Nmult_comm, Nmult_Sn_m.
now rewrite Nplus_comm, Nmult_comm.
Qed.

Theorem le_lt_or_eq : forall n m : N, n <= m <-> n < m \/ n = m.
Proof.
intros n m.
assert (H : (n ?= m) = Eq <-> n = m).
split; intro H; [now apply Ncompare_Eq_eq | rewrite H; apply Ncompare_refl].
unfold Nle, Nlt. rewrite <- H.
destruct (n ?= m); split; intro H1; (try discriminate); try (now left); try now right.
now elim H1. destruct H1; discriminate.
Qed.

Theorem nlt_0_r : forall n : N, ~ (n < 0).
Proof.
unfold Nlt; destruct n as [| p]; simpl; discriminate.
Qed.

Theorem lt_succ_le : forall n m : N, n < (S m) <-> n <= m.
Proof.
intros x y. rewrite le_lt_or_eq.
unfold Nlt, Nle, S; apply Ncompare_n_Sm.
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

Theorem recursion_succ :
  forall (A : Set) (EA : relation A) (a : A) (f : N -> A -> A),
    EA a a -> fun2_wd E EA EA f ->
      forall n : N, EA (recursion a f (Nsucc n)) (f n (recursion a f n)).
Proof.
unfold E, recursion, Nrec, fun2_wd; intros A EA a f EAaa f_wd n; pattern n; apply Nind.
rewrite Nrect_step; rewrite Nrect_base; now apply f_wd.
clear n; intro n; do 2 rewrite Nrect_step; intro IH. apply f_wd; [reflexivity|].
now rewrite Nrect_step.
Qed.

End NBinaryAxiomsMod.

Module Export NBinaryMinusPropMod := NMinusPropFunct NBinaryAxiomsMod.

(*
Module NBinaryDepRec <: NDepRecSignature.
Module Export NDomainModule := NBinaryDomain.
Module Export NBaseMod := BinaryNat.

Definition dep_recursion := Nrec.

Theorem dep_recursion_0 :
  forall (A : N -> Set) (a : A 0) (f : forall n, A n -> A (S n)),
    dep_recursion A a f 0 = a.
Proof.
intros A a f; unfold dep_recursion; unfold Nrec; now rewrite Nrect_base.
Qed.

Theorem dep_recursion_succ :
  forall (A : N -> Set) (a : A 0) (f : forall n, A n -> A (S n)) (n : N),
    dep_recursion A a f (S n) = f n (dep_recursion A a f n).
Proof.
intros A a f n; unfold dep_recursion; unfold Nrec; now rewrite Nrect_step.
Qed.

End NBinaryDepRec.

Module NBinaryPlus <: NPlusSig.
Module Export NBaseMod := BinaryNat.

Definition plus := Nplus.

Add Morphism plus with signature E ==> E ==> E as plus_wd.
Proof.
unfold E; congruence.
Qed.

End NBinaryPlus.

Module NBinaryTimes <: NTimesSig.
Module Export NPlusMod := NBinaryPlus.

Definition times := Nmult.

Add Morphism times with signature E ==> E ==> E as times_wd.
Proof.
unfold E; congruence.
Qed.


End NBinaryTimes.

Module NBinaryOrder <: NOrderSig.
Module Export NBaseMod := BinaryNat.

Definition lt (m n : N) := comp_bool (Ncompare m n) Lt.
Definition le (m n : N) := let c := (Ncompare m n) in orb (comp_bool c Lt) (comp_bool c Eq).

Add Morphism lt with signature E ==> E ==> eq_bool as lt_wd.
Proof.
unfold E; congruence.
Qed.

Add Morphism le with signature E ==> E ==> eq_bool as le_wd.
Proof.
unfold E; congruence.
Qed.

Theorem le_lt : forall n m, le n m <-> lt n m \/ n = m.
Proof.
intros n m.
assert (H : (n ?= m) = Eq <-> n = m).
(split; intro H); [now apply Ncompare_Eq_eq | rewrite H; apply Ncompare_refl].
unfold le, lt; rewrite eq_true_or. repeat rewrite comp_bool_correct. now rewrite H.
Qed.

Theorem lt_0 : forall x, ~ (lt x 0).
Proof.
unfold lt; destruct x as [|x]; simpl; now intro.
Qed.

Theorem lt_succ : forall x y, lt x (S y) <-> le x y.
Proof.
intros x y. rewrite le_lt.
assert (H1 : lt x (S y) <-> Ncompare x (S y) = Lt);
[unfold lt, comp_bool; destruct (x ?= S y); simpl; split; now intro |].
assert (H2 : lt x y <-> Ncompare x y = Lt);
[unfold lt, comp_bool; destruct (x ?= y); simpl; split; now intro |].
pose proof (Ncompare_n_Sm    m x y) as H. tauto.
Qed.

End NBinaryOrder.

Module Export NBinaryTimesOrderProperties := NTimesOrderProperties NBinaryTimes NBinaryOrder.

(* Todo: N implements NPred.v and NMinus.v *)

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

*)
(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
