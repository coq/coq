
(* $Id$ *)

(*i*)
open Term
open Sign
open Evd
open Environ
open Proof_trees
(*i*)

val prim_refiner : prim_rule -> 'a evar_map -> goal -> goal list

val prim_extractor : 
  ((typed_type, constr) env -> proof_tree -> constr) -> 
    (typed_type, constr) env -> proof_tree -> constr

val extract_constr : constr assumptions -> constr -> constr
