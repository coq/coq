(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open EConstr
open Univ
open Evd
open Environ

(** Reduction Functions. *)

exception Elimconst

type meta_handler = { meta_value : metavariable -> EConstr.t option }

val debug_RAKAM : CDebug.t

module CredNative : Primred.RedNative with
  type elem = EConstr.t and type args = EConstr.t array and type evd = Evd.evar_map
  and type uinstance = EInstance.t

(** Machinery to customize the behavior of the reduction *)
module ReductionBehaviour : sig

  type t = NeverUnfold | UnfoldWhen of when_flags | UnfoldWhenNoMatch of when_flags
  and when_flags = { recargs : int list ; nargs : int option }

  module Db : sig
    type t
    val get : unit -> t
    val empty : t
    val print : t -> Constant.t -> Pp.t
    val all_never_unfold : t -> Cpred.t
  end

  val set : local:bool -> Constant.t -> t option -> unit
  val get_from_db : Db.t -> Constant.t -> t option
  val get : Constant.t -> t option
  val print : Constant.t -> Pp.t
end

(** {6 Support for reduction effects } *)

type effect_name = string

(* [declare_reduction_effect name f] declares [f] under key [name];
   [name] must be a unique in "world". *)
val declare_reduction_effect : effect_name ->
  (Environ.env -> Evd.evar_map -> Constr.constr -> unit) -> unit

(* [set_reduction_effect local cst name] declares effect [name] to be called when [cst] is found *)
val set_reduction_effect : Libobject.locality -> Constant.t -> effect_name -> unit

(* [effect_hook env sigma key term] apply effect associated to [key] on [term] *)
val reduction_effect_hook : Environ.env -> Evd.evar_map -> Constant.t ->
  Constr.constr Lazy.t -> unit

module Stack : sig
  type app_node

  val pr_app_node : (EConstr.t -> Pp.t) -> app_node -> Pp.t

  type case_stk

  val mkCaseStk : case_info * EInstance.t * EConstr.t array * EConstr.case_return * EConstr.t pcase_invert * EConstr.case_branch array -> case_stk

  type member =
  | App of app_node
  | Case of case_stk
  | Proj of Projection.t * ERelevance.t
  | Fix of EConstr.fixpoint * t
  | Primitive of CPrimitives.t * (Constant.t * EInstance.t) * t * CPrimitives.args_red
  and t = member list

  val pr : (EConstr.t -> Pp.t) -> t -> Pp.t

  val empty : t
  val is_empty : t -> bool

  val compare_shape : t -> t -> bool

  exception IncompatibleFold2

  (** [fold2 f x sk1 sk2] folds [f] on any pair of term in [(sk1,sk2)].
      @return the result and the lifts to apply on the terms
      @raise IncompatibleFold2 when [sk1] and [sk2] have incompatible shapes *)
  val fold2 : ('a -> constr -> constr -> 'a) -> 'a -> t -> t -> 'a

  (** [append_app args sk] pushes array of arguments [args] on [sk] *)
  val append_app : EConstr.t array -> t -> t

  (** [append_app_list args sk] pushes list of arguments [args] on [sk] *)
  val append_app_list : EConstr.t list -> t -> t

  (** if [strip_app sk] = [(sk1,sk2)], then [sk = sk1 @ sk2] with
      [sk1] purely applicative and [sk2] does not start with an argument *)
  val strip_app : t -> t * t

  (** @return (the nth first elements, the (n+1)th element, the remaining stack)
      if there enough of those *)
  val strip_n_app : int -> t -> (t * EConstr.t * t) option

  (** [decomp sk] extracts the first argument of reversed stack [sk] is there is some *)
  val decomp_rev : t -> (EConstr.t * t) option

  (** [not_purely_applicative sk] *)
  val not_purely_applicative : t -> bool

  (** [list_of_app_stack sk] either returns [Some sk] turned into a list of
      arguments if [sk] is purely applicative and [None] otherwise *)
  val list_of_app_stack : t -> constr list option

  (** [args_size sk] returns the number of arguments available at the
      head of [sk] *)
  val args_size : t -> int

  (** [zip sigma t sk] *)
  val zip : evar_map -> constr * t -> constr

  val expand_case : env -> evar_map -> case_stk ->
    case_info * EInstance.t * constr array * ((rel_context * constr) * ERelevance.t) * (rel_context * constr) array
end

(************************************************************************)

type reduction_function = env -> evar_map -> constr -> constr

type e_reduction_function = env -> evar_map -> constr -> evar_map * constr

type stack_reduction_function =
    env -> evar_map -> constr -> constr * constr list

(** {6 Generic Optimized Reduction Function using Closures } *)

val clos_norm_flags : RedFlags.reds -> reduction_function
val clos_whd_flags : RedFlags.reds -> reduction_function

(** Same as [(strong whd_beta[delta][iota])], but much faster on big terms *)
val nf_beta : reduction_function
val nf_betaiota : reduction_function
val nf_betaiotazeta : reduction_function
val nf_zeta : reduction_function
val nf_all : reduction_function
val nf_evar : evar_map -> constr -> constr

(** Lazy strategy, weak head reduction *)

val whd_evar :  evar_map -> constr -> constr
val whd_nored : ?metas:meta_handler -> reduction_function
val whd_beta : reduction_function
val whd_betaiota : ?metas:meta_handler -> reduction_function
val whd_betaiotazeta : ?metas:meta_handler -> reduction_function
val whd_all : ?metas:meta_handler -> reduction_function
val whd_allnolet :  reduction_function
val whd_betalet : reduction_function

(** Removes cast and put into applicative form *)
val whd_nored_stack : ?metas:meta_handler -> stack_reduction_function
val whd_beta_stack : ?metas:meta_handler -> stack_reduction_function
val whd_betaiota_stack : ?metas:meta_handler -> stack_reduction_function
val whd_betaiotazeta_stack : ?metas:meta_handler -> stack_reduction_function
val whd_all_stack : ?metas:meta_handler -> stack_reduction_function
val whd_allnolet_stack : ?metas:meta_handler -> stack_reduction_function
val whd_betalet_stack : ?metas:meta_handler -> stack_reduction_function

(** {6 Head normal forms } *)

val whd_const : Constant.t -> reduction_function
val whd_delta_stack : ?metas:meta_handler -> stack_reduction_function
val whd_delta :  reduction_function
val whd_betadeltazeta_stack : ?metas:meta_handler -> stack_reduction_function
val whd_betadeltazeta :  reduction_function
val whd_zeta_stack : ?metas:meta_handler -> stack_reduction_function
val whd_zeta : reduction_function

val shrink_eta : evar_map -> constr -> constr

val whd_stack_gen : RedFlags.reds -> ?metas:meta_handler -> stack_reduction_function

(** Various reduction functions *)

val beta_applist : evar_map -> constr * constr list -> constr

val hnf_prod_app     : env -> evar_map -> constr -> constr -> constr
val hnf_prod_appvect : env -> evar_map -> constr -> constr array -> constr
val hnf_prod_applist : env -> evar_map -> constr -> constr list -> constr
val hnf_lam_app      : env -> evar_map -> constr -> constr -> constr
val hnf_lam_appvect  : env -> evar_map -> constr -> constr array -> constr
val hnf_lam_applist  : env -> evar_map -> constr -> constr list -> constr

val whd_decompose_prod : env -> evar_map -> types -> (Name.t EConstr.binder_annot * constr) list * types
(** Decompose a type into a sequence of products and a non-product conclusion
    in head normal form, using head-reduction to expose the products *)

val whd_decompose_lambda : env -> evar_map -> constr -> (Name.t EConstr.binder_annot * constr) list * constr
(** Decompose a term into a sequence of lambdas and a non-lambda conclusion
    in head normal form, using head-reduction to expose the lambdas *)

val whd_decompose_prod_decls : env -> evar_map -> types -> rel_context * types
(** Decompose a type into a context and a conclusion not starting with a product or let-in,
    using head-reduction without zeta to expose the products and let-ins *)

val whd_decompose_prod_n : env -> evar_map -> int -> types -> (Name.t EConstr.binder_annot * constr) list * types
(** Like [whd_decompose_prod] but limited at [n] products; raises [Invalid_argument] if not enough products *)

val whd_decompose_lambda_n : env -> evar_map -> int -> constr -> (Name.t EConstr.binder_annot * constr) list * constr
(** Like [whd_decompose_lambda] but limited at [n] lambdas; raises [Invalid_argument] if not enough lambdas *)

val splay_arity : env -> evar_map -> constr -> (Name.t EConstr.binder_annot * constr) list * ESorts.t
(** Decompose an arity reducing let-ins; Raises [Reduction.NotArity] *)

val dest_arity : env -> evar_map -> constr -> rel_context * ESorts.t
(** Decompose an arity preserving let-ins; Raises [Reduction.NotArity] *)

val sort_of_arity : env -> evar_map -> constr -> ESorts.t
(** Raises [Reduction.NotArity] *)

val whd_decompose_prod_n_assum : env -> evar_map -> int -> types -> rel_context * types
(** Extract the n first products of a type, preserving let-ins (but not counting them);
    Raises [Invalid_argument] if not enough products *)

val whd_decompose_prod_n_decls : env -> evar_map -> int -> types -> rel_context * types
(** Extract the n first products of a type, counting and preserving let-ins;
    Raises [Invalid_argument] if not enough products or let-ins *)

val whd_decompose_lambda_n_assum : env -> evar_map -> int -> constr -> rel_context * constr
(** Extract the n first lambdas of a term, preserving let-ins (but not counting them);
    Raises [Invalid_argument] if not enough lambdas *)

val reducible_mind_case : evar_map -> constr -> bool

val find_conclusion : env -> evar_map -> constr -> (constr, constr, ESorts.t, EInstance.t, ERelevance.t) kind_of_term
val is_arity : env -> evar_map -> constr -> bool
val is_sort : env -> evar_map -> types -> bool

val contract_fix : evar_map -> fixpoint -> constr
val contract_cofix : evar_map -> cofixpoint -> constr

(** {6 Querying the kernel conversion oracle: opaque/transparent constants } *)
val is_transparent : Environ.env -> Evaluable.t -> bool

(** {6 Conversion Functions (uses closures, lazy strategy) } *)

type conversion_test = Constraints.t -> Constraints.t

val is_conv : ?reds:TransparentState.t -> env -> evar_map -> constr -> constr -> bool
val is_conv_leq : ?reds:TransparentState.t -> env -> evar_map -> constr -> constr -> bool
val is_fconv : ?reds:TransparentState.t -> conv_pb -> env -> evar_map -> constr -> constr -> bool

(** [check_conv] Checks universe constraints only.
    pb defaults to CUMUL and ts to a full transparent state.
 *)
val check_conv : ?pb:conv_pb -> ?ts:TransparentState.t -> env -> evar_map -> constr -> constr -> bool
[@@ocaml.deprecated "(8.18) Use Reductionops.is_fconv instead"]

(** [infer_conv] Adds necessary universe constraints to the evar map.
    pb defaults to CUMUL and ts to a full transparent state.
    @raise UniverseInconsistency iff catch_incon is set to false,
    otherwise returns false in that case.
 *)
val infer_conv : ?catch_incon:bool -> ?pb:conv_pb -> ?ts:TransparentState.t ->
  env -> evar_map -> constr -> constr -> evar_map option

val infer_conv_ustate : ?catch_incon:bool -> ?pb:conv_pb -> ?ts:TransparentState.t ->
  env -> evar_map -> constr -> constr -> UnivProblem.Set.t option

(** Conversion with inference of universe constraints *)
val vm_infer_conv : ?pb:conv_pb -> env -> evar_map -> constr -> constr ->
  evar_map option

val native_infer_conv : ?pb:conv_pb -> env -> evar_map -> constr -> constr ->
  evar_map option

type genconv = {
  genconv : 'a 'err. conv_pb -> l2r:bool -> Evd.evar_map -> TransparentState.t ->
    Environ.env -> ('a, 'err) Conversion.generic_conversion_function
}

(** [infer_conv_gen] behaves like [infer_conv] but is parametrized by a
conversion function. Used to pretype vm and native casts. *)
val infer_conv_gen : genconv ->
  ?catch_incon:bool -> ?pb:conv_pb -> ?ts:TransparentState.t -> env ->
  evar_map -> constr -> constr -> evar_map option

val check_hyps_inclusion : env -> evar_map -> GlobRef.t -> Constr.named_context -> unit
(** [Typeops.check_hyps_inclusion] but handles evars in the environment. *)

(** {6 Heuristic for Conversion with Evar } *)

type state = constr * Stack.t

type state_reduction_function =
    env -> evar_map -> state -> state

val pr_state : env -> evar_map -> state -> Pp.t

val whd_nored_state : ?metas:meta_handler -> state_reduction_function

val whd_betaiota_deltazeta_for_iota_state :
  TransparentState.t -> ?metas:meta_handler -> state_reduction_function

exception PatternFailure
val apply_rules : (state -> state) -> env -> evar_map -> EInstance.t ->
  Declarations.rewrite_rule list -> Stack.t -> econstr * Stack.t

val is_head_evar : env -> evar_map -> constr -> bool

exception AnomalyInConversion of exn

(* inferred_universes just gathers the constraints. *)
val inferred_universes : (UGraph.t * Univ.Constraints.t, UGraph.univ_inconsistency) Conversion.universe_compare

(** Deprecated *)

val splay_prod : env -> evar_map -> constr -> (Name.t EConstr.binder_annot * constr) list * constr
[@@ocaml.deprecated "(8.18) Use [whd_decompose_prod] instead."]
val splay_lam : env -> evar_map -> constr -> (Name.t EConstr.binder_annot * constr) list * constr
[@@ocaml.deprecated "(8.18) Use [whd_decompose_lambda] instead."]
val splay_prod_assum : env -> evar_map -> constr -> rel_context * constr
[@@ocaml.deprecated "(8.18) Use [whd_decompose_prod_decls] instead."]
val splay_prod_n : env -> evar_map -> int -> constr -> rel_context * constr
[@@ocaml.deprecated "(8.18) This function contracts let-ins. Replace either with whd_decompose_prod_n (if only products are expected, then returning only a list of assumptions), whd_decompose_prod_n_assum (if let-ins are expected to be preserved, returning a rel_context), or whd_decompose_prod_n_decls (if let-ins are expected to be preserved and counted, returning also a rel_context)"]
val splay_lam_n : env -> evar_map -> int -> constr -> rel_context * constr
[@@ocaml.deprecated "(8.18) This function contracts let-ins. Replace either with whd_decompose_lambda_n (if only lambdas are expected, then returning only a list of assumptions) or whd_decompose_lambda_n_assum (if let-ins are expected to be preserved, returning a rel_context)"]

(** Re-deprecated in 8.19 *)

val hnf_decompose_prod : env -> evar_map -> types -> (Name.t EConstr.binder_annot * constr) list * types
[@@ocaml.deprecated "(8.19) Use [whd_decompose_prod] instead."]
val hnf_decompose_lambda : env -> evar_map -> constr -> (Name.t EConstr.binder_annot * constr) list * constr
[@@ocaml.deprecated "(8.19) Use [whd_decompose_lambda] instead."]
val hnf_decompose_prod_decls : env -> evar_map -> types -> rel_context * types
[@@ocaml.deprecated "(8.19) Use [whd_decompose_prod_decls] instead."]
val hnf_decompose_prod_n_decls : env -> evar_map -> int -> types -> rel_context * types
[@@ocaml.deprecated "(8.19) This function contracts let-ins. Replace either with whd_decompose_prod_n (if only products are expected, then returning only a list of assumptions), whd_decompose_prod_n_assum (if let-ins are expected to be preserved, returning a rel_context), or whd_decompose_prod_n_decls (if let-ins are expected to be preserved and counted, returning also a rel_context)"]
val hnf_decompose_lambda_n_assum : env -> evar_map -> int -> constr -> rel_context * constr
[@@ocaml.deprecated "(8.19) This function contracts let-ins. Replace either with whd_decompose_lambda_n (if only lambdas are expected, then returning only a list of assumptions) or whd_decompose_lambda_n_assum (if let-ins are expected to be preserved, returning a rel_context)"]
