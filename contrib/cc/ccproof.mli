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
  | Refl of term
  | Trans of proof * proof
  | Sym of proof
  | Congr of proof * proof

val up_path :
  (int, UF.cl * 'a * 'b) Hashtbl.t ->
  int ->
  ((int * int) * (int * int * UF.tag)) list ->
  ((int * int) * (int * int * UF.tag)) list

val min_path :
  ('a * 'b) list * ('a * 'c) list ->
  ('a * 'b) list * ('a * 'c) list

val pcongr : proof * proof -> proof
val ptrans : proof * proof -> proof
val psym : proof -> proof
val pcongr : proof * proof -> proof

val build_proof : UF.t -> int -> int -> proof

val type_proof :
  'a ->
  (Names.identifier * (term * term)) list ->
  proof -> term * term

val cc_proof :
  (Names.identifier * (term * term)) list *
  (term * term) ->
  (proof * UF.t *
   (Names.identifier * (term * term)) list)
  option

