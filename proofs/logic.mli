
(* $Id$ *)

(*i*)
open Pp
open Proof_trees
(*i*)

val pr_prim_rule : prim_rule -> std_ppcmds

val prim_refiner : prim_rule -> 'a Evd.evar_map -> goal -> goal list

val prim_extractor : 
  ((type_judgement, constr) env -> proof_tree -> constr) -> 
    (type_judgement, constr) env -> proof_tree -> constr

val extract_constr : constr assumptions -> constr -> constr
