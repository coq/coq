
(* $Id$ *)

(*i*)
open Names
open Term
open Sign
open Evd
open Environ
open Proof_trees
(*i*)

(* The primitive refiner. *)

val prim_refiner : prim_rule -> 'a evar_map -> goal -> goal list

val prim_extractor : 
  ((typed_type, constr) env -> proof_tree -> constr) -> 
    (typed_type, constr) env -> proof_tree -> constr

val extract_constr : constr assumptions -> constr -> constr


(*s Refiner errors. *)

type refiner_error =
  | BadType of constr * constr * constr
  | OccurMeta of constr
  | CannotApply of constr * constr
  | CannotUnify of constr * constr
  | CannotGeneralize of typed_type signature * constr
  | NotWellTyped of constr
  | BadTacticArgs of string * tactic_arg list

val error_cannot_unify : path_kind -> constr * constr -> 'a
