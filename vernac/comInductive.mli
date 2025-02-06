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
  univ_binders : UState.named_universes_entry;
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
  -> variances:Entries.variance_entry
  -> ctx_params:EConstr.rel_context
  -> indnames:Names.Id.t list
  -> arities_explicit:bool list
  -> arities:EConstr.t list
  -> template_syntax:syntax_allows_template_poly list
  -> constructors:(Names.Id.t list * EConstr.constr list) list
  (** Names and types of constructors, not including parameters (as in kernel entries) *)
  -> env_ar:Environ.env
  (** Environment with the inductives in the rel_context *)
  -> private_ind:bool
  -> DeclareInd.default_dep_elim list
     * Entries.mutual_inductive_entry
     * (* for global universe names, used by DeclareInd *)
     UState.named_universes_entry
     * (* global universes to declare before the inductive (ie without the template univs) *)
     Univ.ContextSet.t

(************************************************************************)
(** Internal API, exported for Record                                   *)
(************************************************************************)

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
  val error_differing_params
    : kind:string
    -> (Names.lident * Vernacexpr.inductive_params_expr)
    -> (Names.lident * Vernacexpr.inductive_params_expr)
    -> 'a
end
