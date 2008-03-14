
open Fol

(* generation of the Why file *)

val output_file : string -> query -> unit

(* table to translate the proofs back to Coq (used in dp_zenon) *)

type proof = 
  | Immediate of Term.constr
  | Fun_def of string * (string * typ) list * typ * term

val add_proof : proof -> string
val find_proof : string -> proof


