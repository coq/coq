(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Efficient arbitrary large natural numbers in base 2^31 *)

(** Initial Author: Arnaud Spiwack *)

Require Export Int31 Cyclic31.
Require Import CyclicAxioms Ring31 NSig NSigNAxioms NMake
  NProperties NDiv GenericMinMax.

(** The following [BigN] module regroups both the operations and
    all the abstract properties:

    - [NMake.Make Int31Cyclic] provides the operations and basic specs
       w.r.t. ZArith
    - [NTypeIsNAxioms] shows (mainly) that these operations implement
      the interface [NAxioms]
    - [NPropSig] adds all generic properties derived from [NAxioms]
    - [NDivPropFunct] provides generic properties of [div] and [mod].
    - [MinMax*Properties] provides properties of [min] and [max].

*)

Module BigN <: NType <: OrderedTypeFull <: TotalOrder :=
 NMake.Make Int31Cyclic <+ NTypeIsNAxioms
 <+ !NPropSig <+ !NDivPropFunct <+ HasEqBool2Dec
 <+ !MinMaxLogicalProperties <+ !MinMaxDecProperties.


(** Notations about [BigN] *)

Notation bigN := BigN.t.

Delimit Scope bigN_scope with bigN.
Bind Scope bigN_scope with bigN.
Bind Scope bigN_scope with BigN.t.
Bind Scope bigN_scope with BigN.t_.
(* Bind Scope has no retroactive effect, let's declare scopes by hand. *)
Arguments Scope BigN.to_Z [bigN_scope].
Arguments Scope BigN.succ [bigN_scope].
Arguments Scope BigN.pred [bigN_scope].
Arguments Scope BigN.square [bigN_scope].
Arguments Scope BigN.add [bigN_scope bigN_scope].
Arguments Scope BigN.sub [bigN_scope bigN_scope].
Arguments Scope BigN.mul [bigN_scope bigN_scope].
Arguments Scope BigN.div [bigN_scope bigN_scope].
Arguments Scope BigN.eq [bigN_scope bigN_scope].
Arguments Scope BigN.lt [bigN_scope bigN_scope].
Arguments Scope BigN.le [bigN_scope bigN_scope].
Arguments Scope BigN.eq [bigN_scope bigN_scope].
Arguments Scope BigN.compare [bigN_scope bigN_scope].
Arguments Scope BigN.min [bigN_scope bigN_scope].
Arguments Scope BigN.max [bigN_scope bigN_scope].
Arguments Scope BigN.eq_bool [bigN_scope bigN_scope].
Arguments Scope BigN.power_pos [bigN_scope positive_scope].
Arguments Scope BigN.power [bigN_scope N_scope].
Arguments Scope BigN.sqrt [bigN_scope].
Arguments Scope BigN.div_eucl [bigN_scope bigN_scope].
Arguments Scope BigN.modulo [bigN_scope bigN_scope].
Arguments Scope BigN.gcd [bigN_scope bigN_scope].

Local Notation "0" := BigN.zero : bigN_scope. (* temporary notation *)
Local Notation "1" := BigN.one : bigN_scope. (* temporary notation *)
Infix "+" := BigN.add : bigN_scope.
Infix "-" := BigN.sub : bigN_scope.
Infix "*" := BigN.mul : bigN_scope.
Infix "/" := BigN.div : bigN_scope.
Infix "^" := BigN.power : bigN_scope.
Infix "?=" := BigN.compare : bigN_scope.
Infix "==" := BigN.eq (at level 70, no associativity) : bigN_scope.
Notation "x != y" := (~x==y)%bigN (at level 70, no associativity) : bigN_scope.
Infix "<" := BigN.lt : bigN_scope.
Infix "<=" := BigN.le : bigN_scope.
Notation "x > y" := (BigN.lt y x)(only parsing) : bigN_scope.
Notation "x >= y" := (BigN.le y x)(only parsing) : bigN_scope.
Notation "x < y < z" := (x<y /\ y<z)%bigN : bigN_scope.
Notation "x < y <= z" := (x<y /\ y<=z)%bigN : bigN_scope.
Notation "x <= y < z" := (x<=y /\ y<z)%bigN : bigN_scope.
Notation "x <= y <= z" := (x<=y /\ y<=z)%bigN : bigN_scope.
Notation "[ i ]" := (BigN.to_Z i) : bigN_scope.
Infix "mod" := BigN.modulo (at level 40, no associativity) : bigN_scope.

Local Open Scope bigN_scope.

(** Example of reasoning about [BigN] *)

Theorem succ_pred: forall q : bigN,
  0 < q -> BigN.succ (BigN.pred q) == q.
Proof.
intros; apply BigN.succ_pred.
intro H'; rewrite H' in H; discriminate.
Qed.

(** [BigN] is a semi-ring *)

Lemma BigNring : semi_ring_theory 0 1 BigN.add BigN.mul BigN.eq.
Proof.
constructor.
exact BigN.add_0_l. exact BigN.add_comm. exact BigN.add_assoc.
exact BigN.mul_1_l. exact BigN.mul_0_l. exact BigN.mul_comm.
exact BigN.mul_assoc. exact BigN.mul_add_distr_r.
Qed.

Lemma BigNeqb_correct : forall x y, BigN.eq_bool x y = true -> x==y.
Proof. now apply BigN.eqb_eq. Qed.

Lemma BigNpower : power_theory 1 BigN.mul BigN.eq (@id N) BigN.power.
Proof.
constructor.
intros. red. rewrite BigN.spec_power. unfold id.
destruct Zpower_theory as [EQ]. rewrite EQ.
destruct n; simpl. reflexivity.
induction p; simpl; intros; BigN.zify; rewrite ?IHp; auto.
Qed.

Lemma BigNdiv : div_theory BigN.eq BigN.add BigN.mul (@id _)
 (fun a b => if BigN.eq_bool b 0 then (0,a) else BigN.div_eucl a b).
Proof.
constructor. unfold id. intros a b.
BigN.zify.
generalize (Zeq_bool_if [b] 0); destruct (Zeq_bool [b] 0).
BigN.zify. auto with zarith.
intros NEQ.
generalize (BigN.spec_div_eucl a b).
generalize (Z_div_mod_full [a] [b] NEQ).
destruct BigN.div_eucl as (q,r), Zdiv_eucl as (q',r').
intros (EQ,_). injection 1. intros EQr EQq.
BigN.zify. rewrite EQr, EQq; auto.
Qed.


(** Detection of constants *)

Ltac isStaticWordCst t :=
 match t with
 | W0 => constr:true
 | WW ?t1 ?t2 =>
   match isStaticWordCst t1 with
   | false => constr:false
   | true => isStaticWordCst t2
   end
 | _ => isInt31cst t
 end.

Ltac isBigNcst t :=
 match t with
 | BigN.N0 ?t => isStaticWordCst t
 | BigN.N1 ?t => isStaticWordCst t
 | BigN.N2 ?t => isStaticWordCst t
 | BigN.N3 ?t => isStaticWordCst t
 | BigN.N4 ?t => isStaticWordCst t
 | BigN.N5 ?t => isStaticWordCst t
 | BigN.N6 ?t => isStaticWordCst t
 | BigN.Nn ?n ?t => match isnatcst n with
   | true => isStaticWordCst t
   | false => constr:false
   end
 | BigN.zero => constr:true
 | BigN.one => constr:true
 | _ => constr:false
 end.

Ltac BigNcst t :=
 match isBigNcst t with
 | true => constr:t
 | false => constr:NotConstant
 end.

Ltac Ncst t :=
 match isNcst t with
 | true => constr:t
 | false => constr:NotConstant
 end.

(** Registration for the "ring" tactic *)

Add Ring BigNr : BigNring
 (decidable BigNeqb_correct,
  constants [BigNcst],
  power_tac BigNpower [Ncst],
  div BigNdiv).

Section TestRing.
Let test : forall x y, 1 + x*y + x^2 + 1 == 1*1 + 1 + y*x + 1*x*x.
intros. ring_simplify. reflexivity.
Qed.
End TestRing.

(** We benefit also from an "order" tactic *)

Ltac bigN_order := BigN.order.

Section TestOrder.
Let test : forall x y : bigN, x<=y -> y<=x -> x==y.
Proof. bigN_order. Qed.
End TestOrder.

(** We can use at least a bit of (r)omega by translating to [Z]. *)

Section TestOmega.
Let test : forall x y : bigN, x<=y -> y<=x -> x==y.
Proof. intros x y. BigN.zify. omega. Qed.
End TestOmega.

(** Todo: micromega *)
