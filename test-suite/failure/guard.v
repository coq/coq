(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*
Fixpoint F (n:nat) : False := F (match F n with end).
*)
(* de Bruijn mix-up *)
(* If accepted, Eval compute in f 0. loops *)
Fail Definition f :=
  let f (f1 f2:nat->nat) := f1 in
  let _ := 0 in
  let _ := 0 in
  let g (f1 f2:nat->nat) := f2 in
  let h := f in (* h = Rel 4 *)
  fix F (n:nat) : nat :=
  h F S n. (* here Rel 4 = g *)

