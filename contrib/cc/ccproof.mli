(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Ccalgo
open Names

type proof =
    Ax of identifier
  | SymAx of identifier
  | Refl of term
  | Trans of proof * proof
  | Congr of proof * proof
  | Inject of proof * constructor * int * int

val pcongr : proof * proof -> proof
val ptrans : proof * proof -> proof
val psym : proof -> proof
val pcongr : proof * proof -> proof

val build_proof : 
  UF.t -> 
  [ `Discriminate of int * int * int * int
  | `Prove_goal of int * int
  | `Refute_hyp of int * int ]
  -> proof

val type_proof :
  (identifier * (term * term)) list -> proof -> term * term

val cc_proof :
  (identifier * (term * term)) list ->
  (identifier * (term * term)) list ->
  (term * term) option ->
  [ `Discriminate of constructor * proof
  | `Prove_goal of proof
  | `Refute_hyp of identifier * proof ]


