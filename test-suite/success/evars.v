(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(* The "?" of cons and eq should be inferred *)
Variable list:Set -> Set.
Variable cons:(T:Set) T -> (list T) -> (list T).
Goal (n:(list nat)) (EX l| (EX x| (n = (cons ? x l)))).

