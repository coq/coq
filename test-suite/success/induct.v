(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(* Teste des definitions inductives imbriquees *)

Require PolyList.

Inductive X : Set := 
    cons1 : (list X)->X.

Inductive Y : Set := 
    cons2 : (list Y*Y)->Y.

