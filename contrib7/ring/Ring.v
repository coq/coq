(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Require Export Bool.
Require Export Ring_theory.
Require Export Quote.
Require Export Ring_normalize.
Require Export Ring_abstract.

(* As an example, we provide an instantation for bool. *)
(* Other instatiations are given in ArithRing and ZArithRing in the
   same directory *)

Definition BoolTheory : (Ring_Theory xorb andb true false [b:bool]b eqb).
Split; Simpl.
NewDestruct n; NewDestruct m; Reflexivity.
NewDestruct n; NewDestruct m; NewDestruct p; Reflexivity.
NewDestruct n; NewDestruct m; Reflexivity.
NewDestruct n; NewDestruct m; NewDestruct p; Reflexivity.
NewDestruct n; Reflexivity.
NewDestruct n; Reflexivity.
NewDestruct n; Reflexivity.
NewDestruct n; NewDestruct m; NewDestruct p; Reflexivity.
NewDestruct x; NewDestruct y; Reflexivity Orelse Simpl; Tauto.
Defined.

Add Ring bool xorb andb true false [b:bool]b eqb BoolTheory [ true false ].
