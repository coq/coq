
(* $Id$ *)

(*i*)
open Pp
open Term
open Sign
open Proof_trees
(*i*)

val pr_prim_rule : prim_rule -> std_ppcmds

val prim_refiner : prim_rule -> Evd.evar_map -> goal -> goal list

val prim_extractor : 
  ((typed_type, constr) env -> proof_tree -> constr) -> 
    (typed_type, constr) env -> proof_tree -> constr

val extract_constr : constr assumptions -> constr -> constr
