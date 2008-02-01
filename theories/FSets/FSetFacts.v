(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(** * Finite sets library *)

(** This functor derives additional facts from [FSetInterface.S]. These
  facts are mainly the specifications of [FSetInterface.S] written using 
  different styles: equivalence and boolean equalities. 
  Moreover, we prove that [E.Eq] and [Equal] are setoid equalities.

  We now simply reuse facts proved for weak sets (those without 
  order on elements).
*)

Require Import DecidableTypeEx.
Require Export FSetInterface.
Require FSetWeakFacts.

Module Facts (M:S).
 Module D:=OT_as_DT M.E.
 Include FSetWeakFacts.Facts M D.
End Facts.
