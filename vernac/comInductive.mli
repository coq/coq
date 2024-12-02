(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Vernacexpr
open Constrexpr

(** {6 Inductive and coinductive types} *)

type flags = {
  poly : bool;
  cumulative : bool;
  template : bool option;
  auto_prop_lowering : bool;
  finite : Declarations.recursivity_kind;
  mode : Hints.hint_mode list option;
}

(** Entry points for the vernacular commands Inductive and CoInductive *)

type uniform_inductive_flag =
  | UniformParameters
  | NonUniformParameters

val do_mutual_inductive
  : flags:flags
  -> ?typing_flags:Declarations.typing_flags
  -> cumul_univ_decl_expr option
  -> (one_inductive_expr * notation_declaration list) list
  -> private_ind:bool
  -> uniform:uniform_inductive_flag
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
  default_dep_elim : DeclareInd.default_dep_elim list;
  nuparams : int option;
  univ_binders : UnivNames.universe_binders;
  implicits : DeclareInd.one_inductive_impls list;
  uctx : Univ.ContextSet.t;
  where_notations : Metasyntax.notation_interpretation_decl list;
  coercions : Libnames.qualid list;
  indlocs : DeclareInd.indlocs;
}

end

(** elaborates an inductive declaration (the first half of do_mutual_inductive) *)
val interp_mutual_inductive
  :  env:Environ.env
  -> flags:flags
  -> ?typing_flags:Declarations.typing_flags
  -> cumul_univ_decl_expr option
  -> (one_inductive_expr * notation_declaration list) list
  -> private_ind:bool
  -> uniform:uniform_inductive_flag
  -> Mind_decl.t

type syntax_allows_template_poly = SyntaxAllowsTemplatePoly | SyntaxNoTemplatePoly

(** the post-elaboration part of interp_mutual_inductive, mainly dealing with
    universe levels *)
val interp_mutual_inductive_constr
  :  sigma:Evd.evar_map
  -> flags:flags
  -> udecl:UState.universe_decl
  -> ctx_params:EConstr.rel_context
  -> indnames:Names.Id.t list
  -> arities_explicit:bool list
  -> arities:EConstr.t list
  -> template_syntax:syntax_allows_template_poly list
  -> constructors:(Names.Id.t list * EConstr.constr list) list
  -> env_ar_params:Environ.env
  (** Environment with the inductives and parameters in the rel_context *)
  -> private_ind:bool
  -> DeclareInd.default_dep_elim list * Entries.mutual_inductive_entry * UnivNames.universe_binders * Univ.ContextSet.t

(************************************************************************)
(** Internal API, exported for Record                                   *)
(************************************************************************)

val compute_template_inductive
  : user_template:bool option
  -> ctx_params:Constr.rel_context
  -> univ_entry:UState.universes_entry
  -> Entries.one_inductive_entry
  -> syntax_allows_template_poly
  -> Entries.inductive_universes_entry * Univ.ContextSet.t
(** [compute_template_inductive] computes whether an inductive can be template
    polymorphic. *)

val maybe_unify_params_in : Environ.env -> Evd.evar_map -> ninds:int -> nparams:int -> binders:int
  -> EConstr.t -> Evd.evar_map
(** [nparams] is the number of parameters which aren't treated as
    uniform, ie the length of params (including letins) where the env
    is [uniform params, inductives, params, binders]. *)

val variance_of_entry
  : cumulative:bool
  -> UVars.UContext.t
  -> UVars.variances option -> UVars.variances option
(** The identity if non-cumulative, and resize if there are more
    universes than originally specified.
    If monomorphic, [cumulative] is treated as [false].
*)

module Internal :
sig
  (** Returns the modified arities (the result sort may be replaced by Prop).
      Should be called with minimized universes. *)
  val inductive_levels
    : auto_prop_lowering:bool
    -> Environ.env
    -> Evd.evar_map
    -> poly:bool
    -> indnames:Names.Id.t list
    -> arities_explicit:bool list
    (* whether the arities were explicit from the user (for auto Prop lowering) *)
    -> EConstr.constr list
    (* arities *)
    -> EConstr.rel_context list list
    (* constructors *)
    -> Evd.evar_map * (DeclareInd.default_dep_elim list * EConstr.t list)

  val error_differing_params
    : kind:string
    -> (Names.lident * Vernacexpr.inductive_params_expr)
    -> (Names.lident * Vernacexpr.inductive_params_expr)
    -> 'a

end
