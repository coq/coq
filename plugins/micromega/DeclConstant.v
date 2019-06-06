(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

Class GT {T : Type} (F : T).

Instance GT_O {T : Type} (F : T) {DC : DeclaredConstant F} : GT F.
Defined.

Instance GT_APP1 {T1 T2 : Type} (F : T1 -> T2) (A : T1) :
  DeclaredConstant F ->
  GT A -> GT (F A).
Defined.

Instance GT_APP2 {T1 T2 T3: Type} (F : T1 -> T2 -> T3)
         {A1 : T1} {A2 : T2} {DC:DeclaredConstant F} :
         GT A1 -> GT A2 -> GT (F A1 A2).
Defined.

Require Import ZArith.

Instance DO : DeclaredConstant O := {}.
Instance DS : DeclaredConstant S := {}.
Instance DxH: DeclaredConstant xH := {}.
Instance DxI: DeclaredConstant xI := {}.
Instance DxO: DeclaredConstant xO := {}.
Instance DZO: DeclaredConstant Z0 := {}.
Instance DZpos: DeclaredConstant Zpos := {}.
Instance DZneg: DeclaredConstant Zneg := {}.
Instance DZpow_pos : DeclaredConstant Z.pow_pos := {}.
Instance DZpow     : DeclaredConstant Z.pow     := {}.

Require Import QArith.

Instance DQ : DeclaredConstant Qmake := {}.
