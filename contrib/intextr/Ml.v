(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(************************************************************************)
(*                                                                      *)
(* Representation of mini-ML terms                                      *)
(*                                                                      *)
(* Originally by Zaynah Dargaye (CompCert project, INRIA Rocquencourt)  *)
(*                                                                      *)
(************************************************************************)

(* $Id$ *)

Require Import List.

(***** Premier langage intermédiaire Pml en indices de de Bruijn *****)

Inductive term : Set :=
  | TDummy : term
  | TVar : nat -> term
  | TLet : term -> term -> term
  | TFun : term -> term
  | TFix : term -> term
  | TApply : term -> term -> term
  | TConstr : nat -> list term -> term
    (* les constructeurs des types concrets sont representés par des numéros *)
  | TMatch : term -> list pat -> term
with pat : Set :=
  | Patc : nat -> term -> pat
    (* le nat est le nombre d'arguments du constructeur *)
.

Notation "a @ b" := (TApply a b) (at level 40, left associativity).

(* Pourrait être une coercion *)
Definition unpat p := match p with Patc n t => t end.


(***** Principe d'induction mutuelle entre les term et les list term *****)

Section term_ind2.
  Variable P : term -> Prop.
  Variable Q : list term -> Prop.

  Let Pp p := P (unpat p).
  Let Qp l := Q (map unpat l).

(*
  Variable Pp : pat -> Prop.
  Variable Qp : list pat -> Prop.
  Hypothesis Hp : forall n t, P t -> Pp (Patc n t).
  Hypothesis Hpnil : Qp nil.
  Hypothesis Hpcons : forall p pl, Pp p -> Qp pl -> Qp (p::pl).
*)

  Hypothesis HDummy : P TDummy.
  Hypothesis HVar : forall n, P (TVar n).
  Hypothesis HFun : forall f, P f -> P (TFun f).
  Hypothesis HFix : forall f, P f -> P (TFix f).
  Hypothesis HLet : forall a1 a2, P a1 -> P a2 -> P (TLet a1 a2).
  Hypothesis HApply : forall a1 a2, P a1 -> P a2 -> P (TApply a1 a2).
  Hypothesis HConstr : forall c l, Q l -> P (TConstr c l).
  Hypothesis HMatch : forall t pl, P t -> Qp pl -> P (TMatch t pl).

  Hypothesis Hnil : Q nil.
  Hypothesis Hcons : forall a l, P a -> Q l -> Q (a::l).

  Fixpoint term_ind2 t : P t :=
    match t as t0 return P t0 with
      | TDummy => HDummy
      | TVar n => HVar n
      | TFun f => HFun f (term_ind2 f)
      | TFix f => HFix f (term_ind2 f)
      | TLet a1 a2 => HLet a1 a2 (term_ind2 a1) (term_ind2 a2)
      | TApply a1 a2 => HApply a1 a2 (term_ind2 a1) (term_ind2 a2)
      | TConstr c l => HConstr c l
          ((fix F (l : list term) := match l as l0 return Q l0 with
              | nil => Hnil
              | cons a l => Hcons a l (term_ind2 a) (F l)
            end) l)
      | TMatch t pl => HMatch t pl (term_ind2 t)
          ((fix F (pl : list pat) := match pl as l0 return Qp l0 with
              | nil => Hnil
              | cons p pl => Hcons (unpat p) (map unpat pl) (term_ind2 (unpat p)) (F pl)
            end) pl)
    end.
End term_ind2.
