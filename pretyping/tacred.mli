
(* $Id$ *)

(*i*)
open Names
open Term
open Environ
open Evd
open Reduction
(*i*)

(* Reduction functions associated to tactics. \label{tacred} *)

val hnf_constr : 'a reduction_function

val nf : 'a reduction_function

val one_step_reduce : 'a reduction_function

val reduce_to_mind : 
  env -> 'a evar_map -> constr -> inductive * constr * constr

val reduce_to_ind : 
  env -> 'a evar_map -> constr -> section_path * constr * constr

type red_expr =
  | Red
  | Hnf
  | Simpl
  | Cbv of Closure.flags
  | Lazy of Closure.flags
  | Unfold of (int list * section_path) list
  | Fold of constr list
  | Pattern of (int list * constr * constr) list

val reduction_of_redexp : red_expr -> 'a reduction_function

