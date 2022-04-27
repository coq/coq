(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Vernacexpr
open Constrexpr

(** {6 Inductive and coinductive types} *)

(** Entry points for the vernacular commands Inductive and CoInductive *)

type uniform_inductive_flag =
  | UniformParameters
  | NonUniformParameters

val do_mutual_inductive
  :  template:bool option
  -> cumul_univ_decl_expr option
  -> (one_inductive_expr * decl_notation list) list
  -> cumulative:bool
  -> poly:bool
  -> ?typing_flags:Declarations.typing_flags
  -> private_ind:bool
  -> uniform:uniform_inductive_flag
  -> Declarations.recursivity_kind
  -> unit

(** User-interface API *)

(** Prepare a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables.
    [Not_found] is raised if the given string isn't the qualid of
    a known inductive type. *)

val make_cases : Names.inductive -> string list list

module Mind_decl : sig

(** inductive_expr at the constr level *)
type t = {
  mie : Entries.mutual_inductive_entry;
  nuparams : int option;
  univ_binders : UnivNames.universe_binders;
  implicits : DeclareInd.one_inductive_impls list;
  uctx : Univ.ContextSet.t;
  where_notations : Metasyntax.where_decl_notation list;
  coercions : Libnames.qualid list;
}

end

(** elaborates an inductive declaration (the first half of do_mutual_inductive) *)
val interp_mutual_inductive
  :  env:Environ.env
  -> template:bool option
  -> cumul_univ_decl_expr option
  -> (one_inductive_expr * decl_notation list) list
  -> cumulative:bool
  -> poly:bool
  -> ?typing_flags:Declarations.typing_flags
  -> private_ind:bool
  -> uniform:uniform_inductive_flag
  -> Declarations.recursivity_kind
  -> Mind_decl.t

(** the post-elaboration part of interp_mutual_inductive, mainly dealing with
    universe levels *)
val interp_mutual_inductive_constr
  : sigma:Evd.evar_map
  -> template:bool option
  -> udecl:UState.universe_decl
  -> variances:Entries.variance_entry
  -> ctx_params:(EConstr.t, EConstr.t) Context.Rel.Declaration.pt list
  -> indnames:Names.Id.t list
  -> arities:EConstr.t list
  -> arityconcl:(bool * EConstr.ESorts.t) option list
  -> constructors:(Names.Id.t list * Constr.constr list) list
  -> env_ar_params:Environ.env
  (** Environment with the inductives and parameters in the rel_context *)
  -> cumulative:bool
  -> poly:bool
  -> private_ind:bool
  -> finite:Declarations.recursivity_kind
  -> Entries.mutual_inductive_entry * UnivNames.universe_binders * Univ.ContextSet.t

(************************************************************************)
(** Internal API, exported for Record                                   *)
(************************************************************************)

val should_auto_template : Id.t -> bool -> bool
(** [should_auto_template x b] is [true] when [b] is [true] and we
   automatically use template polymorphism. [x] is the name of the
   inductive under consideration. *)

val template_polymorphism_candidate
  : ctor_levels:Univ.Level.Set.t
  -> UState.universes_entry
  -> Constr.rel_context
  -> Sorts.t option
  -> bool
(** [template_polymorphism_candidate ~ctor_levels uctx params
   conclsort] is [true] iff an inductive with params [params],
   conclusion [conclsort] and universe levels appearing in the
   constructor arguments [ctor_levels] would be definable as template
   polymorphic. It should have at least one universe in its
   monomorphic universe context that can be made parametric in its
   conclusion sort, if one is given. *)

val maybe_unify_params_in : Environ.env -> Evd.evar_map -> ninds:int -> nparams:int -> binders:int
  -> EConstr.t -> Evd.evar_map
(** [nparams] is the number of parameters which aren't treated as
    uniform, ie the length of params (including letins) where the env
    is [uniform params, inductives, params, binders]. *)

val variance_of_entry
  : cumulative:bool
  -> variances:Entries.variance_entry
  -> Entries.inductive_universes_entry
  -> Entries.variance_entry option
(** Will return None if non-cumulative, and resize if there are more
    universes than originally specified.
    If monomorphic, [cumulative] is treated as [false].
*)

module Internal :
sig
  val compute_constructor_level : Environ.env -> Evd.evar_map -> EConstr.rel_context -> Sorts.t
end
