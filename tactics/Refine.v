(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Declare ML Module "refine".

Grammar tactic simple_tactic: ast :=
  tcc [ "Refine" castedopenconstrarg($c) ] -> [(Tcc $c)].

Syntax tactic level 0:
  tcc [ (Refine $C) ] -> ["Refine " $C].
