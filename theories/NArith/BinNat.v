(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i i*)

Require Import BinPos.
Require Import NBinDefs.

(*Unset Boxed Definitions.*)

Delimit Scope N_scope with N.
Bind Scope N_scope with N.
Open Local Scope N_scope.

(** Operations *)

Notation N := N (only parsing).
Notation N0 := N0 (only parsing).
Notation Npos := Npos (only parsing).
Notation Nsucc := succ (only parsing).
Notation Npred := pred (only parsing).
Notation Nplus := plus (only parsing).
Notation Nminus := minus (only parsing).
Notation Nmult := times (only parsing).
Notation Ncompare := Ncompare (only parsing).
Notation Nlt := lt (only parsing).
Notation Nle := le (only parsing).
Definition Ngt (x y : N) := (Ncompare x y) = Gt.
Definition Nge (x y : N) := (Ncompare x y) <> Lt.
Notation Nmin := min (only parsing).
Notation Nmax := max (only parsing).

(* If the notations for operations above had been actual definitions, the
arguments scopes would have been N_scope due to the instruction "Bind Scope
N_scope with N". However, the operations were declared in NBinary, where
N_scope has not yet been declared. Therefore, we need to assign the
arguments scopes manually. Note that this has to be done before declaring
infix notations below. Ngt and Nge get their scope from the definition. *)

Arguments Scope succ [N_scope].
Arguments Scope pred [N_scope].
Arguments Scope plus [N_scope N_scope].
Arguments Scope minus [N_scope N_scope].
Arguments Scope times [N_scope N_scope].
Arguments Scope NBinDefs.Ncompare [N_scope N_scope].
Arguments Scope lt [N_scope N_scope].
Arguments Scope le [N_scope N_scope].
Arguments Scope min [N_scope N_scope].
Arguments Scope max [N_scope N_scope].

Infix "+" := Nplus : N_scope.
Infix "-" := Nminus : N_scope.
Infix "*" := Nmult : N_scope.
Infix "?=" := Ncompare (at level 70, no associativity) : N_scope.
Infix "<=" := Nle : N_scope.
Infix "<" := Nlt : N_scope.
Infix ">=" := Nge : N_scope.
Infix ">" := Ngt : N_scope.

(** Peano induction and recursion *)

Notation Nrect := Nrect (only parsing).
Notation Nrect_base := Nrect_base (only parsing).
Notation Nrect_step := Nrect_step (only parsing).
Definition Nind (P : N -> Prop) := Nrect P.
Definition Nrec (P : N -> Set) := Nrect P.

Theorem Nrec_base : forall P a f, Nrec P a f N0 = a.
Proof.
intros P a f; unfold Nrec; apply Nrect_base.
Qed.

Theorem Nrec_step : forall P a f n, Nrec P a f (Nsucc n) = f n (Nrec P a f n).
Proof.
intros P a f; unfold Nrec; apply Nrect_step.
Qed.

(** Properties of successor and predecessor *)

Notation Npred_succ := pred_succ (only parsing).
Notation Nsucc_0 := neq_succ_0 (only parsing).
Notation Nsucc_inj := succ_inj (only parsing).

(** Properties of addition *)

Notation Nplus_0_l := plus_0_l (only parsing).
Notation Nplus_0_r := plus_0_r (only parsing).
Notation Nplus_comm := plus_comm (only parsing).
Notation Nplus_assoc := plus_assoc (only parsing).
Notation Nplus_succ := plus_succ_l (only parsing).
Notation Nplus_reg_l := (fun n m p : N => proj1 (plus_cancel_l m p n)) (only parsing).

(** Properties of subtraction. *)

Notation Nminus_N0_Nle := minus_0_le (only parsing).
Notation Nminus_0_r := minus_0_r (only parsing).
Notation Nminus_succ_r := minus_succ_r (only parsing).

(** Properties of multiplication *)

Notation Nmult_0_l := times_0_l (only parsing).
Notation Nmult_1_l := times_1_l (only parsing).
Notation Nmult_1_r := times_1_r (only parsing).
Theorem Nmult_Sn_m : forall n m : N, (Nsucc n) * m = m + n * m.
Proof.
intros; now rewrite times_succ_l, Nplus_comm.
Qed.
Notation Nmult_comm := times_comm (only parsing).
Notation Nmult_assoc := times_assoc (only parsing).
Notation Nmult_plus_distr_r := times_plus_distr_r (only parsing).
Notation Nmult_reg_r :=
  (fun (n m p : N) (H : p <> N0) => proj1 (times_cancel_r n m p H)) (only parsing).

(** Properties of comparison *)

Notation Ncompare_Eq_eq := (fun n m : N => proj1 (Ncompare_eq_correct n m)) (only parsing).
Notation Ncompare_refl := Ncompare_diag (only parsing).
Notation Nlt_irrefl := lt_irrefl (only parsing).

Lemma Ncompare_antisym : forall n m, CompOpp (n ?= m) = (m ?= n).
Proof.
destruct n; destruct m; simpl; auto.
exact (Pcompare_antisym p p0 Eq).
Qed.

Theorem Ncompare_0 : forall n : N, Ncompare n N0 <> Lt.
Proof.
destruct n; discriminate.
Qed.

(** Other properties and operations; given explicitly *)

Definition Ndiscr : forall n : N, {p : positive | n = Npos p} + {n = N0}.
Proof.
destruct n; auto.
left; exists p; auto.
Defined.

(** Operation x -> 2 * x + 1 *)

Definition Ndouble_plus_one x :=
match x with
| N0 => Npos 1
| Npos p => Npos (xI p)
end.

(** Operation x -> 2 * x *)

Definition Ndouble n :=
match n with
| N0 => N0
| Npos p => Npos (xO p)
end.

(** convenient induction principles *)

Theorem N_ind_double :
 forall (a:N) (P:N -> Prop),
   P N0 ->
   (forall a, P a -> P (Ndouble a)) ->
   (forall a, P a -> P (Ndouble_plus_one a)) -> P a.
Proof.
  intros; elim a. trivial.
  simple induction p. intros.
  apply (H1 (Npos p0)); trivial.
  intros; apply (H0 (Npos p0)); trivial.
  intros; apply (H1 N0); assumption.
Qed.

Lemma N_rec_double :
 forall (a:N) (P:N -> Set),
   P N0 ->
   (forall a, P a -> P (Ndouble a)) ->
   (forall a, P a -> P (Ndouble_plus_one a)) -> P a.
Proof.
  intros; elim a. trivial.
  simple induction p. intros.
  apply (H1 (Npos p0)); trivial.
  intros; apply (H0 (Npos p0)); trivial.
  intros; apply (H1 N0); assumption.
Qed.

(** Division by 2 *)

Definition Ndiv2 (n:N) :=
  match n with
  | N0 => N0
  | Npos 1 => N0
  | Npos (xO p) => Npos p
  | Npos (xI p) => Npos p
  end.

Lemma Ndouble_div2 : forall n:N, Ndiv2 (Ndouble n) = n.
Proof.
  destruct n; trivial.
Qed.

Lemma Ndouble_plus_one_div2 :
 forall n:N, Ndiv2 (Ndouble_plus_one n) = n.
Proof.
  destruct n; trivial.
Qed.

Lemma Ndouble_inj : forall n m, Ndouble n = Ndouble m -> n = m.
Proof.
  intros. rewrite <- (Ndouble_div2 n). rewrite H. apply Ndouble_div2.
Qed.

Lemma Ndouble_plus_one_inj :
 forall n m, Ndouble_plus_one n = Ndouble_plus_one m -> n = m.
Proof.
  intros. rewrite <- (Ndouble_plus_one_div2 n). rewrite H. apply Ndouble_plus_one_div2.
Qed.

