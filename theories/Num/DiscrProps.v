(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(*i $Id$ i*)

Require Export DiscrAxioms.
Require Export LtProps.

(*s Properties of a discrete order *)

Lemma lt_le_Sx_y : (x,y:N)(x<y) -> ((S x)<=y).
EAuto with num.
Save.
Hints Resolve lt_le_Sx_y : num.