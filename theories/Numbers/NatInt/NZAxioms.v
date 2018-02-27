(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Initial Author : Evgeny Makarov, INRIA, 2007 *)

Require Export Equalities Orders NumPrelude GenericMinMax.

(** Axiomatization of a domain with zero, successor, predecessor,
    and a bi-directional induction principle. We require [P (S n) = n]
    but not the other way around, since this domain is meant
    to be either N or Z. In fact it can be a few other things,
    for instance [Z/nZ] (See file [NZDomain] for a study of that).
*)

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

Module Type IsNZDomain (Import E:Eq')(Import NZ:ZeroSuccPred' E).
 Declare Instance succ_wd : Proper (eq ==> eq) S.
 Declare Instance pred_wd : Proper (eq ==> eq) P.
 Axiom pred_succ : forall n, P (S n) == n.
 Axiom bi_induction :
  forall A : t -> Prop, Proper (eq==>iff) A ->
    A 0 -> (forall n, A n <-> A (S n)) -> forall n, A n.
End IsNZDomain.

(** Axiomatization of some more constants

    Simply denoting "1" for (S 0) and so on works ok when implementing
    by nat, but leaves some (N.succ N0) when implementing by N.
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

(** Axiomatization of basic operations : [+] [-] [*] *)

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
 Declare Instance add_wd : Proper (eq ==> eq ==> eq) add.
 Declare Instance sub_wd : Proper (eq ==> eq ==> eq) sub.
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

(** Axiomatization of order *)

Module Type NZOrd := NZDomainSig <+ HasLt <+ HasLe.
Module Type NZOrd' := NZDomainSig' <+ HasLt <+ HasLe <+
                      LtNotation <+ LeNotation <+ LtLeNotation.

Module Type IsNZOrd (Import NZ : NZOrd').
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

Module Type NZOrdAxiomsSig <: NZBasicFunsSig <: NZOrdSig
 := NZOrdSig <+ AddSubMul <+ IsAddSubMul <+ HasMinMax.
Module Type NZOrdAxiomsSig' <: NZOrdAxiomsSig
 := NZOrdSig' <+ AddSubMul' <+ IsAddSubMul <+ HasMinMax.


(** Same, plus a comparison function. *)

Module Type NZDecOrdSig := NZOrdSig <+ HasCompare.
Module Type NZDecOrdSig' := NZOrdSig' <+ HasCompare.

Module Type NZDecOrdAxiomsSig := NZOrdAxiomsSig <+ HasCompare.
Module Type NZDecOrdAxiomsSig' := NZOrdAxiomsSig' <+ HasCompare.

(** A square function *)

Module Type NZSquare (Import NZ : NZBasicFunsSig').
 Parameter Inline square : t -> t.
 Axiom square_spec : forall n, square n == n * n.
End NZSquare.
