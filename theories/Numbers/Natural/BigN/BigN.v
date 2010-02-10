(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Efficient arbitrary large natural numbers in base 2^31 *)

(** Initial Author: Arnaud Spiwack *)

Require Export Int31.
Require Import CyclicAxioms Cyclic31 NSig NSigNAxioms NMake
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
Arguments Scope BigN.sqrt [bigN_scope].
Arguments Scope BigN.div_eucl [bigN_scope bigN_scope].
Arguments Scope BigN.modulo [bigN_scope bigN_scope].
Arguments Scope BigN.gcd [bigN_scope bigN_scope].

Local Notation "0" := BigN.zero : bigN_scope. (* temporary notation *)
Infix "+" := BigN.add : bigN_scope.
Infix "-" := BigN.sub : bigN_scope.
Infix "*" := BigN.mul : bigN_scope.
Infix "/" := BigN.div : bigN_scope.
Infix "^" := BigN.power_pos : bigN_scope.
Infix "?=" := BigN.compare : bigN_scope.
Infix "==" := BigN.eq (at level 70, no associativity) : bigN_scope.
Infix "<" := BigN.lt : bigN_scope.
Infix "<=" := BigN.le : bigN_scope.
Notation "x > y" := (BigN.lt y x)(only parsing) : bigN_scope.
Notation "x >= y" := (BigN.le y x)(only parsing) : bigN_scope.
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

Lemma BigNring :
 semi_ring_theory BigN.zero BigN.one BigN.add BigN.mul BigN.eq.
Proof.
constructor.
exact BigN.add_0_l.
exact BigN.add_comm.
exact BigN.add_assoc.
exact BigN.mul_1_l.
exact BigN.mul_0_l.
exact BigN.mul_comm.
exact BigN.mul_assoc.
exact BigN.mul_add_distr_r.
Qed.

Add Ring BigNr : BigNring.

(** We benefit from an "order" tactic *)

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
