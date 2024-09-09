(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Initial Author : Evgeny Makarov, INRIA, 2007 *)

(** * Axioms for a domain with [zero], [succ], [pred], [le] and [lt] *)

(** This file is the starting point of a modular and axiomatic development of
natural numbers and integers. The files and modules in [Coq.Numbers.NatInt]
contain specifications and proofs which are common to natural numbers and
integers. The files and modules in [Coq.Numbers.Natural.Abstract] give specific
results about natural numbers, with the extra axiom that the predecessor of 0
is 0, while the sublibrary [Coq.Numbers.Integer.Abstract] give specific
results about integers, with the extra axiom that successor and predecessor
are one-to-one correspondences.

The module type [NZDomainSig'] specifies a type [t] with:
- a general equality [eq], denoted by [==] and its negation [neq] denoted by [~=],
- a constant [zero] denoted by [0] and unary operators [succ] and [pred],
  denoted by [S] and [P] satisfying
  - [pred_succ : forall n, P (S n) == n]
  - [bi_induction], a bidirectional induction principle centered at [0]
- the constants [1 = S 0] and [2 = S 1]

The module type [NZOrdSig'] further assumes the existence of the predicates
[le] (denoted by [<=]) and [lt] (denoted by [<]) satisfying
- [lt_eq_cases : forall n m : t, n <= m <-> n < m \/ n == m]
- [lt_irrefl : forall n : t, ~ n < n]
- [lt_succ_r : forall n m : t, n < S m <-> n <= m]
The combined specification, imposes that the models of this theory are
infinite. There are two cases:
- either [S] is surjective, in which case we have integers
- or there exists a unique initial point [i <= 0] such that [S (P i) ~= i],
  in which case we have natural numbers, possibly shifted on the left; the
  predecessor of the initial point being arbitrary.

The interested reader can refer to [Coq.Numbers.NatInt.NZOrder], in particular
[lt_exists_pred], [lt_succ_pred] and the module type [NatIntOrderProp].

This underspecification in the natural case prevented to state common results
about subtraction, therefore we complete it with the module type [IsNatInt]
which further imposes:
- [Private_succ_pred : forall n, n ~= 0 -> S (P n) == n]
- [le_pred_l : forall n, P n <= n]
In the natural case, this forces the initial point to be [0] and [P 0 == 0].
So this restricts the models to only natural numbers or integers.
The module type [IsNatInt] is currently kept separate from all the other module
types for technical and historical reasons.

The module type [NZBasicFunsSig'] adds to [NZDomainSig'] the operations [add],
[sub] and [mul] denoted by [+], [-] and [*] respectively, satisfying
- [add_0_l : forall n, 0 + n == n]
- [add_succ_l : forall n m, (S n) + m == S (n + m)]
- [sub_0_r : forall n, n - 0 == n]
- [sub_succ_r : forall n m, n - (S m) == P (n - m)]
- [mul_0_l : forall n, 0 * n == 0]
- [mul_succ_l : forall n m, S n * m == n * m + m]

We build the module type [NZOrdAxiomsSig'] by adding the orders as well as
[min] and [max] functions consistent with [le].

Finally, [NZDecOrdAxiomsSig'] is obtained by adding a three-valued [compare]
function, therefore imposing that equality and orders are decidable.
*)

From Coq.Structures Require Export Equalities Orders.

(** We use the [Equalities] module in order to work with a general decidable
equality [eq]. The [Orders] module contains module types about orders [lt] and
[le] in [Prop]. *)

From Coq.Numbers Require Export NumPrelude.

From Coq.Structures Require Export GenericMinMax.
(** The [GenericMinMax] module gives specifications and basic lemmas for [min]
 and [max] operators on ordered types. *)

(** ** Axiomatization of a domain with [zero], [succ], [pred] and a bi-directional induction principle *)

(** The [Typ] module type in [Equalities] has a unique parameter [t : Type]. *)

Module Type ZeroSuccPred (Import T:Typ).
 Parameter Inline(20) zero : t.
 Parameter Inline(50) succ : t -> t.
 Parameter Inline pred : t -> t.
End ZeroSuccPred.

Module Type ZeroSuccPredNotation (T:Typ)(Import NZ:ZeroSuccPred T).
 Notation "0" := zero.
 Notation S := succ.
 Notation P := pred.
End ZeroSuccPredNotation.

Module Type ZeroSuccPred' (T:Typ) :=
 ZeroSuccPred T <+ ZeroSuccPredNotation T.

(** The [Eq'] module type in [Equalities] is a [Type] [t] with a binary predicate
    [eq] denoted by [==]. The negation of [==] is denoted by [~=]. *)

Module Type IsNZDomain (Import E:Eq')(Import NZ:ZeroSuccPred' E).
#[global]
 Declare Instance succ_wd : Proper (eq ==> eq) S.
#[global]
 Declare Instance pred_wd : Proper (eq ==> eq) P.
 Axiom pred_succ : forall n, P (S n) == n.
 Axiom bi_induction :
  forall A : t -> Prop, Proper (eq==>iff) A ->
    A 0 -> (forall n, A n <-> A (S n)) -> forall n, A n.
End IsNZDomain.

(* Simply denoting "1" for (S 0) and so on works ok when implementing
by [nat], but leaves some ([N.succ N0]) when implementing by [N]. *)

Module Type OneTwo (Import T:Typ).
 Parameter Inline(20) one two : t.
End OneTwo.

Module Type OneTwoNotation (T:Typ)(Import NZ:OneTwo T).
 Notation "1" := one.
 Notation "2" := two.
End OneTwoNotation.

Module Type OneTwo' (T:Typ) := OneTwo T <+ OneTwoNotation T.

Module Type IsOneTwo (E:Eq')(Z:ZeroSuccPred' E)(O:OneTwo' E).
 Import E Z O.
 Axiom one_succ : 1 == S 0.
 Axiom two_succ : 2 == S 1.
End IsOneTwo.

Module Type NZDomainSig :=
 EqualityType <+ ZeroSuccPred <+ IsNZDomain <+ OneTwo <+ IsOneTwo.
Module Type NZDomainSig' :=
 EqualityType' <+ ZeroSuccPred' <+ IsNZDomain <+ OneTwo' <+ IsOneTwo.

(** ** Axiomatization of order *)

(** The module type [HasLt] (resp. [HasLe]) is just a type equipped with
a relation [lt] (resp. [le]) in [Prop]. *)

Module Type NZOrd := NZDomainSig <+ HasLt <+ HasLe.
Module Type NZOrd' := NZDomainSig' <+ HasLt <+ HasLe <+
                      LtNotation <+ LeNotation <+ LtLeNotation.

Module Type IsNZOrd (Import NZ : NZOrd').
#[global]
 Declare Instance lt_wd : Proper (eq ==> eq ==> iff) lt.
 Axiom lt_eq_cases : forall n m, n <= m <-> n < m \/ n == m.
 Axiom lt_irrefl : forall n, ~ (n < n).
 Axiom lt_succ_r : forall n m, n < S m <-> n <= m.
End IsNZOrd.

(* NB: the compatibility of [le] can be proved later from [lt_wd] and
[lt_eq_cases]. *)

Module Type NZOrdSig := NZOrd <+ IsNZOrd.
Module Type NZOrdSig' := NZOrd' <+ IsNZOrd.

Module Type IsNatInt (Import NZ : NZOrdSig').
 Axiom Private_succ_pred : forall n, n ~= 0 -> S (P n) == n.
 Axiom le_pred_l : forall n, P n <= n.
End IsNatInt.

(** ** Axiomatization of basic operations : [+] [-] [*] *)

Module Type AddSubMul (Import T:Typ).
 Parameters Inline add sub mul : t -> t -> t.
End AddSubMul.

Module Type AddSubMulNotation (T:Typ)(Import NZ:AddSubMul T).
 Notation "x + y" := (add x y).
 Notation "x - y" := (sub x y).
 Notation "x * y" := (mul x y).
End AddSubMulNotation.

Module Type AddSubMul' (T:Typ) := AddSubMul T <+ AddSubMulNotation T.

Module Type IsAddSubMul (Import E:NZDomainSig')(Import NZ:AddSubMul' E).
#[global]
 Declare Instance add_wd : Proper (eq ==> eq ==> eq) add.
#[global]
 Declare Instance sub_wd : Proper (eq ==> eq ==> eq) sub.
#[global]
 Declare Instance mul_wd : Proper (eq ==> eq ==> eq) mul.
 Axiom add_0_l : forall n, 0 + n == n.
 Axiom add_succ_l : forall n m, (S n) + m == S (n + m).
 Axiom sub_0_r : forall n, n - 0 == n.
 Axiom sub_succ_r : forall n m, n - (S m) == P (n - m).
 Axiom mul_0_l : forall n, 0 * n == 0.
 Axiom mul_succ_l : forall n m, S n * m == n * m + m.
End IsAddSubMul.

Module Type NZBasicFunsSig := NZDomainSig <+ AddSubMul <+ IsAddSubMul.
Module Type NZBasicFunsSig' := NZDomainSig' <+ AddSubMul' <+IsAddSubMul.

(** ** Everything together with [min], [max] and [compare] functions *)

(** The [HasMinMax] module type is a type with [min] and [max] operators
consistent with [le]. *)

Module Type NZOrdAxiomsSig <: NZBasicFunsSig <: NZOrdSig
 := NZOrdSig <+ AddSubMul <+ IsAddSubMul <+ HasMinMax.
Module Type NZOrdAxiomsSig' <: NZOrdAxiomsSig
 := NZOrdSig' <+ AddSubMul' <+ IsAddSubMul <+ HasMinMax.

(** The [HasCompare] module type requires a comparison function in type
[comparison] consistent with [eq] and [lt]. In particular, this imposes
that the order is decidable. *)

Module Type NZDecOrdSig := NZOrdSig <+ HasCompare.
Module Type NZDecOrdSig' := NZOrdSig' <+ HasCompare.

Module Type NZDecOrdAxiomsSig := NZOrdAxiomsSig <+ HasCompare.
Module Type NZDecOrdAxiomsSig' := NZOrdAxiomsSig' <+ HasCompare.

(** A square function *)

(* TODO: why is this here? *)
Module Type NZSquare (Import NZ : NZBasicFunsSig').
 Parameter Inline square : t -> t.
 Axiom square_spec : forall n, square n == n * n.
End NZSquare.
