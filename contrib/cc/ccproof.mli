(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Ccalgo

type proof =
    Ax of Names.identifier
  | SymAx of Names.identifier
  | Refl of term
  | Trans of proof * proof
  | Congr of proof * proof
  | Inject of proof * Names.constructor * int * int

val pcongr : proof * proof -> proof
val ptrans : proof * proof -> proof
val psym : proof -> proof
val pcongr : proof * proof -> proof

type ('a,'b) mission=
    Prove of 'a
  | Refute of 'b

val build_proof : UF.t -> (int * int, int * int * int * int) mission -> proof

val type_proof :
  (Names.identifier * (term * term)) list -> proof -> term * term

val cc_proof :
  (Names.identifier * (term * term)) list * (term * term) option ->
  (proof * (Names.identifier * (term * term)) list, 
   term * term * proof * (Names.identifier * (term * term)) list ) mission

