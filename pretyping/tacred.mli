
(*i $Id$ i*)

(*i*)
open Names
open Term
open Environ
open Evd
open Reduction
(*i*)

(*s Reduction functions associated to tactics. \label{tacred} *)

exception Redelimination

(* Red (raise Redelimination if nothing reducible) *)
val red_product : 'a reduction_function

(* Hnf *)
val hnf_constr : 'a reduction_function

(* Simpl *)
val nf : 'a reduction_function

(* Unfold *)
val unfoldn : (int list * section_path) list -> 'a reduction_function

(* Fold *)
val fold_commands : constr list -> 'a reduction_function

(* Pattern *)
val pattern_occs : (int list * constr * constr) list -> 'a reduction_function
(* Rem: Lazy strategies are defined in Reduction *)

(* Call by value strategy (uses Closures) *)
val cbv_norm_flags : Closure.flags -> 'a reduction_function
  val cbv_beta : 'a reduction_function
  val cbv_betaiota : 'a reduction_function
  val cbv_betadeltaiota : 'a reduction_function
  val compute : 'a reduction_function  (* = [cbv_betadeltaiota] *)

val one_step_reduce : 'a reduction_function

val reduce_to_mind : 
  env -> 'a evar_map -> constr -> inductive * constr * constr

val reduce_to_ind : 
  env -> 'a evar_map -> constr -> section_path * constr * constr

type red_expr =
  | Red of bool    (* raise Redelimination if true otherwise UserError *)
  | Hnf
  | Simpl
  | Cbv of Closure.flags
  | Lazy of Closure.flags
  | Unfold of (int list * section_path) list
  | Fold of constr list
  | Pattern of (int list * constr * constr) list

val reduction_of_redexp : red_expr -> 'a reduction_function

