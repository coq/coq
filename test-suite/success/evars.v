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

(* Examples provided by Eduardo Gimenez *)

Definition c [A,P] := [p:nat*A]let (i,v) = p in (P i v).

Require PolyList.
Definition list_forall_bool  [A:Set][p:A->bool][l:(list A)] : bool := 
 (fold_right ([a][r]if (p a) then r else false) true l).