(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(* Dependent elimination of some logical notions. *)

Scheme eq_indd  := Induction for eq  Sort Prop.
Scheme eqT_indd := Induction for eqT Sort Prop.
Scheme or_indd  := Induction for or  Sort Prop.
