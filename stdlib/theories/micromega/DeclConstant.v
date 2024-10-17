(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2019                                  *)
(*                                                                      *)
(************************************************************************)

(** Declaring 'allowed' terms using type classes.

    Motivation: reification needs to know which terms are allowed.
    For 'lia', the constant are only the integers built from Z0, Zpos, Zneg, xH, xO, xI.
    However, if the term is ground it may be convertible to an integer.
    Thus we could allow i.e. sqrt z for some integer z.

    Proposal: for each type, the user declares using type-classes the set of allowed ground terms.
 *)

Require Import List.

(**  Declarative definition of constants.
     These are ground terms (without variables) of interest.
     e.g. nat is built from O and S
     NB: this does not need to be restricted to constructors.
 *)

(** Ground terms (see [GT] below) are built inductively from declared constants. *)

Class DeclaredConstant {T : Type} (F : T).
Register DeclaredConstant as micromega.DeclaredConstant.type.

Class GT {T : Type} (F : T).

#[global]
Instance GT_O {T : Type} (F : T) {DC : DeclaredConstant F} : GT F.
Defined.

#[global]
Instance GT_APP1 {T1 T2 : Type} (F : T1 -> T2) (A : T1) :
  DeclaredConstant F ->
  GT A -> GT (F A).
Defined.

#[global]
Instance GT_APP2 {T1 T2 T3: Type} (F : T1 -> T2 -> T3)
         {A1 : T1} {A2 : T2} {DC:DeclaredConstant F} :
         GT A1 -> GT A2 -> GT (F A1 A2).
Defined.

Require Import QArith_base.

#[global]
Instance DO : DeclaredConstant O := {}.
#[global]
Instance DS : DeclaredConstant S := {}.
#[global]
Instance DxH: DeclaredConstant xH := {}.
#[global]
Instance DxI: DeclaredConstant xI := {}.
#[global]
Instance DxO: DeclaredConstant xO := {}.
#[global]
Instance DZO: DeclaredConstant Z0 := {}.
#[global]
Instance DZpos: DeclaredConstant Zpos := {}.
#[global]
Instance DZneg: DeclaredConstant Zneg := {}.
#[global]
Instance DZpow_pos : DeclaredConstant Z.pow_pos := {}.
#[global]
Instance DZpow     : DeclaredConstant Z.pow     := {}.

#[global]
Instance DQ : DeclaredConstant Qmake := {}.
