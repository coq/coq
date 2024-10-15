(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Initial Author : Evgeny Makarov, INRIA, 2007 *)

(** * Axioms for a domain with [zero], [succ], [pred]. *)

From Stdlib.Structures Require Export Equalities Orders.

(** We use the [Equalities] module in order to work with a general decidable
    equality [eq]. *)

(** The [Orders] module contains module types about orders [lt] and [le] in
    [Prop].
*)

From Stdlib.Numbers Require Export NumPrelude.

From Stdlib.Structures Require Export GenericMinMax.
(** The [GenericMinMax] module adds specifications and basic lemmas for [min]
   and [max] operators on ordered types. *)


(** At the end of the day, this file defines the module types
    [NZDecOrdAxiomsSig] and [NZDecOrdAxiomsSig'] (with notations) :
[[
Module Type
 NZDecOrdAxiomsSig' =
 Sig
   Parameter t : Type.
   Parameter eq : t -> t -> Prop.
   Parameter eq_equiv : Equivalence eq.
   Parameter zero : t.
   Parameter succ : t -> t.
   Parameter pred : t -> t.
   Parameter succ_wd : Proper (eq ==> eq) succ.
   Parameter pred_wd : Proper (eq ==> eq) pred.
   Parameter pred_succ : forall n : t, eq (pred (succ n)) n.
   Parameter bi_induction :
     forall A : t -> Prop,
     Proper (eq ==> iff) A ->
     A zero -> (forall n : t, A n <-> A (succ n)) -> forall n : t, A n.
   Parameter one : t.
   Parameter two : t.
   Parameter one_succ : eq one (succ zero).
   Parameter two_succ : eq two (succ one).
   Parameter lt : t -> t -> Prop.
   Parameter le : t -> t -> Prop.
   Parameter lt_wd : Proper (eq ==> eq ==> iff) lt.
   Parameter lt_eq_cases : forall n m : t, le n m <-> lt n m \/ eq n m.
   Parameter lt_irrefl : forall n : t, ~ lt n n.
   Parameter lt_succ_r : forall n m : t, lt n (succ m) <-> le n m.
   Parameter add : t -> t -> t.
   Parameter sub : t -> t -> t.
   Parameter mul : t -> t -> t.
   Parameter add_wd : Proper (eq ==> eq ==> eq) add.
   Parameter sub_wd : Proper (eq ==> eq ==> eq) sub.
   Parameter mul_wd : Proper (eq ==> eq ==> eq) mul.
   Parameter add_0_l : forall n : t, eq (add zero n) n.
   Parameter add_succ_l :
     forall n m : t, eq (add (succ n) m) (succ (add n m)).
   Parameter sub_0_r : forall n : t, eq (sub n zero) n.
   Parameter sub_succ_r :
     forall n m : t, eq (sub n (succ m)) (pred (sub n m)).
   Parameter mul_0_l : forall n : t, eq (mul zero n) zero.
   Parameter mul_succ_l :
     forall n m : t, eq (mul (succ n) m) (add (mul n m) m).
   Parameter max : t -> t -> t.
   Parameter max_l : forall x y : t, le y x -> eq (max x y) x.
   Parameter max_r : forall x y : t, le x y -> eq (max x y) y.
   Parameter min : t -> t -> t.
   Parameter min_l : forall x y : t, le x y -> eq (min x y) x.
   Parameter min_r : forall x y : t, le y x -> eq (min x y) y.
   Parameter compare : t -> t -> comparison.
   Parameter compare_spec :
     forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
 End
]]
 *)

(** ** Axiomatization of a domain with [zero], [succ], [pred] and a bi-directional induction principle. *)

(* NB: This was Pierre Letouzey's conclusion in the (now deprecated) NZDomain
   file. *)
(** We require [P (S n) = n] but not the other way around, since this domain
    is meant to be either N or Z. In fact it can be a few other things,

    S is always injective, P is always surjective  (thanks to [pred_succ]).

    I) If S is not surjective, we have an initial point, which is unique.
       This bottom is below zero: we have N shifted (or not) to the left.
       P cannot be injective: P init = P (S (P init)).
       (P init) can be arbitrary.

    II) If S is surjective, we have [forall n, S (P n) = n], S and P are
       bijective and reciprocal.

       IIa) if [exists k<>O, 0 == S^k 0], then we have a cyclic structure Z/nZ
       IIb) otherwise, we have Z
*)

(** The [Typ] module type in [Equalities] only has a parameter [t : Type]. *)

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
    [eq] denoted [==]. The negation of [==] is denoted [~=]. *)

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

(** ** Axiomatization of some more constants *)

(** Simply denoting "1" for (S 0) and so on works ok when implementing
    by [nat], but leaves some ([N.succ N0]) when implementing by [N].
*)

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

(** At this point, a module implementing [NZDomainSig] has :
- two unary operators [pred] and [succ] such that
  [forall n, pred (succ n) = n].
- a bidirectional induction principle
- three constants [0], [1 = S 0], [2 = S 1]
*)

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

(** Old name for the same interface: *)

Module Type NZAxiomsSig := NZBasicFunsSig.
Module Type NZAxiomsSig' := NZBasicFunsSig'.

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

(** NB: the compatibility of [le] can be proved later from [lt_wd]
    and [lt_eq_cases] *)

Module Type NZOrdSig := NZOrd <+ IsNZOrd.
Module Type NZOrdSig' := NZOrd' <+ IsNZOrd.

(** Everything together : *)

(** The [HasMinMax] module type is a type with [min] and [max] operators
   consistent with [le]. *)

Module Type NZOrdAxiomsSig <: NZBasicFunsSig <: NZOrdSig
 := NZOrdSig <+ AddSubMul <+ IsAddSubMul <+ HasMinMax.
Module Type NZOrdAxiomsSig' <: NZOrdAxiomsSig
 := NZOrdSig' <+ AddSubMul' <+ IsAddSubMul <+ HasMinMax.


(** Same, plus a comparison function. *)

(** The [HasCompare] module type requires a comparison function in type
    [comparison] consistent with [eq] and [lt]. In particular, this imposes
    that the order is decidable.
*)

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
