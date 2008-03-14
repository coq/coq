open Ascent;;
open Evd;;
open Proof_type;;
open Environ;;
open Term;;

val translate_goal : goal -> ct_RULE;;
val translate_goals : goal list -> ct_RULE_LIST;;
(* The boolean argument indicates whether names from the environment should *)
(*  be avoided (same interpretation as for prterm_env and ast_of_constr)    *)
val translate_constr : bool -> env -> constr -> ct_FORMULA;;
val translate_path : int list -> ct_SIGNED_INT_LIST;;
