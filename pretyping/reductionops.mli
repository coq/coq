(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Context
open Univ
open Evd
open Environ
open Closure

(** Reduction Functions. *)

exception Elimconst

module Stack : sig
  (** 90% copy-paste of kernel/closure.ml but polymorphic and with extra
      arguments for storing refold *)
  type 'a member =
  | App of 'a list
  | Case of case_info * 'a * 'a array * ('a * 'a list) option
  | Fix of fixpoint * 'a t * ('a * 'a list) option
  | Shift of int
  | Update of 'a
  and 'a t = 'a member list

  val pr : ('a -> Pp.std_ppcmds) -> 'a t -> Pp.std_ppcmds

  val empty : 'a t
  val compare_shape : 'a t -> 'a t -> bool
  (** [fold2 f x sk1 sk2] folds [f] on any pair of term in [(sk1,sk2)].
      @return the result and the lifts to apply on the terms *)
  val fold2 : ('a -> Term.constr -> Term.constr -> 'a) -> 'a ->
    Term.constr t -> Term.constr t -> 'a * int * int
  val append_app : 'a array -> 'a t -> 'a t
  val append_app_list : 'a list -> 'a t -> 'a t

  val decomp : 'a t -> ('a * 'a t) option
  val strip_app : 'a t -> 'a list * 'a t
  (** Takes the n first arguments of application put on the stack. Fails is the
      stack does not start by n arguments of application. *)
  val nfirsts_app : int -> 'a t -> 'a list
  (** @return (the nth first elements, the (n+1)th element, the remaining stack)  *)
  val strip_n_app : int -> 'a t -> ('a list * 'a * 'a t) option

  val not_purely_applicative : 'a t -> bool
  val list_of_app_stack : 'a t -> 'a list option
  val array_of_app_stack : 'a t -> 'a array option

  val assign : 'a t -> int -> 'a -> 'a t
  val args_size : 'a t -> int
  val tail : int -> 'a t -> 'a t
  val nth : 'a t -> int -> 'a

  val zip : ?refold:bool -> constr * constr t -> constr
end

(************************************************************************)

type state = constr * constr Stack.t

type contextual_reduction_function = env -> evar_map -> constr -> constr
type reduction_function = contextual_reduction_function
type local_reduction_function = evar_map -> constr -> constr

type contextual_stack_reduction_function =
    env -> evar_map -> constr -> constr * constr list
type stack_reduction_function = contextual_stack_reduction_function
type local_stack_reduction_function =
    evar_map -> constr -> constr * constr list

type contextual_state_reduction_function =
    env -> evar_map -> state -> state
type state_reduction_function = contextual_state_reduction_function
type local_state_reduction_function = evar_map -> state -> state

val pr_state : state -> Pp.std_ppcmds

(** {6 Machinery about a stack of unfolded constant }

    cst applied to params must convertible to term of the state applied to args
*)
module Cst_stack : sig
  type t
  val empty : t
  val add_param : constr -> t -> t
  val add_args : constr array -> t -> t
  val add_cst : constr -> t -> t
  val best_cst : t -> (constr * constr list) option
end

(** {6 Reduction Function Operators } *)

val strong : reduction_function -> reduction_function
val local_strong : local_reduction_function -> local_reduction_function
val strong_prodspine : local_reduction_function -> local_reduction_function
(*i
val stack_reduction_of_reduction :
  'a reduction_function -> 'a state_reduction_function
i*)
val stacklam : (state -> 'a) -> constr list -> constr -> constr Stack.t -> 'a

val whd_state_gen : ?csts:Cst_stack.t -> bool -> Closure.RedFlags.reds ->
  Environ.env -> Evd.evar_map -> state -> state * Cst_stack.t

(** {6 Generic Optimized Reduction Function using Closures } *)

val clos_norm_flags : Closure.RedFlags.reds -> reduction_function

(** Same as [(strong whd_beta[delta][iota])], but much faster on big terms *)
val nf_beta : local_reduction_function
val nf_betaiota : local_reduction_function
val nf_betaiotazeta : local_reduction_function
val nf_betadeltaiota : reduction_function
val nf_evar : evar_map -> constr -> constr

val nf_betaiota_preserving_vm_cast : reduction_function

(** Lazy strategy, weak head reduction *)

val whd_evar :  evar_map -> constr -> constr
val whd_nored : local_reduction_function
val whd_beta : local_reduction_function
val whd_betaiota : local_reduction_function
val whd_betaiotazeta : local_reduction_function
val whd_betadeltaiota :  contextual_reduction_function
val whd_betadeltaiota_nolet :  contextual_reduction_function
val whd_betaetalet : local_reduction_function
val whd_betalet : local_reduction_function

(** Removes cast and put into applicative form *)
val whd_nored_stack : local_stack_reduction_function
val whd_beta_stack : local_stack_reduction_function
val whd_betaiota_stack : local_stack_reduction_function
val whd_betaiotazeta_stack : local_stack_reduction_function
val whd_betadeltaiota_stack : contextual_stack_reduction_function
val whd_betadeltaiota_nolet_stack : contextual_stack_reduction_function
val whd_betaetalet_stack : local_stack_reduction_function
val whd_betalet_stack : local_stack_reduction_function

val whd_nored_state : local_state_reduction_function
val whd_beta_state : local_state_reduction_function
val whd_betaiota_state : local_state_reduction_function
val whd_betaiotazeta_state : local_state_reduction_function
val whd_betadeltaiota_state : contextual_state_reduction_function
val whd_betadeltaiota_nolet_state : contextual_state_reduction_function
val whd_betaetalet_state : local_state_reduction_function
val whd_betalet_state : local_state_reduction_function

(** {6 Head normal forms } *)

val whd_delta_stack :  stack_reduction_function
val whd_delta_state :  state_reduction_function
val whd_delta :  reduction_function
val whd_betadelta_stack :  stack_reduction_function
val whd_betadelta_state :  state_reduction_function
val whd_betadelta :  reduction_function
val whd_betadeltaeta_stack :  stack_reduction_function
val whd_betadeltaeta_state :  state_reduction_function
val whd_betadeltaeta :  reduction_function
val whd_betadeltaiotaeta_stack :  stack_reduction_function
val whd_betadeltaiotaeta_state :  state_reduction_function
val whd_betadeltaiotaeta :  reduction_function

val whd_eta : constr -> constr
val whd_zeta : constr -> constr

(** Various reduction functions *)

val safe_evar_value : evar_map -> existential -> constr option

val beta_applist : constr * constr list -> constr

val hnf_prod_app     : env ->  evar_map -> constr -> constr -> constr
val hnf_prod_appvect : env ->  evar_map -> constr -> constr array -> constr
val hnf_prod_applist : env ->  evar_map -> constr -> constr list -> constr
val hnf_lam_app      : env ->  evar_map -> constr -> constr -> constr
val hnf_lam_appvect  : env ->  evar_map -> constr -> constr array -> constr
val hnf_lam_applist  : env ->  evar_map -> constr -> constr list -> constr

val splay_prod : env ->  evar_map -> constr -> (Name.t * constr) list * constr
val splay_lam : env ->  evar_map -> constr -> (Name.t * constr) list * constr
val splay_arity : env ->  evar_map -> constr -> (Name.t * constr) list * sorts
val sort_of_arity : env -> evar_map -> constr -> sorts
val splay_prod_n : env ->  evar_map -> int -> constr -> rel_context * constr
val splay_lam_n : env ->  evar_map -> int -> constr -> rel_context * constr
val splay_prod_assum :
  env ->  evar_map -> constr -> rel_context * constr

type 'a miota_args = {
  mP      : constr;     (** the result type *)
  mconstr : constr;     (** the constructor *)
  mci     : case_info;  (** special info to re-build pattern *)
  mcargs  : 'a list;    (** the constructor's arguments *)
  mlf     : 'a array }  (** the branch code vector *)

val reducible_mind_case : constr -> bool
val reduce_mind_case : constr miota_args -> constr

val find_conclusion : env -> evar_map -> constr -> (constr,constr) kind_of_term
val is_arity : env ->  evar_map -> constr -> bool
val is_sort : env -> evar_map -> types -> bool

val whd_programs :  reduction_function

val contract_fix : ?env:Environ.env -> fixpoint ->
  (constr * constr list) option -> constr
val fix_recarg : fixpoint -> constr Stack.t -> (int * constr) option

(** {6 Querying the kernel conversion oracle: opaque/transparent constants } *)
val is_transparent : Environ.env -> 'a tableKey -> bool

(** {6 Conversion Functions (uses closures, lazy strategy) } *)

type conversion_test = constraints -> constraints

val pb_is_equal : conv_pb -> bool
val pb_equal : conv_pb -> conv_pb

val sort_cmp : conv_pb -> sorts -> sorts -> conversion_test

val is_conv : env ->  evar_map -> constr -> constr -> bool
val is_conv_leq : env ->  evar_map -> constr -> constr -> bool
val is_fconv : conv_pb -> env ->  evar_map -> constr -> constr -> bool

val is_trans_conv : transparent_state -> env -> evar_map -> constr -> constr -> bool
val is_trans_conv_leq : transparent_state -> env ->  evar_map -> constr -> constr -> bool
val is_trans_fconv : conv_pb -> transparent_state -> env ->  evar_map -> constr -> constr -> bool

(** {6 Special-Purpose Reduction Functions } *)

val whd_meta : evar_map -> constr -> constr
val plain_instance : constr Metamap.t -> constr -> constr
val instance : evar_map -> constr Metamap.t -> constr -> constr
val head_unfold_under_prod : transparent_state -> reduction_function

(** {6 Heuristic for Conversion with Evar } *)

val whd_betaiota_deltazeta_for_iota_state :
  transparent_state -> Environ.env -> Evd.evar_map -> Cst_stack.t -> state ->
  state * Cst_stack.t

(** {6 Meta-related reduction functions } *)
val meta_instance : evar_map -> constr freelisted -> constr
val nf_meta       : evar_map -> constr -> constr
val meta_reducible_instance : evar_map -> constr freelisted -> constr
