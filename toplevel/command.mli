(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Entries
open Libnames
open Globnames
open Tacexpr
open Vernacexpr
open Constrexpr
open Decl_kinds
open Redexpr
open Pfedit

(** This file is about the interpretation of raw commands into typed
    ones and top-level declaration of the main Gallina objects *)

val do_universe : Id.t Loc.located list -> unit
val do_constraint : (Id.t Loc.located * Univ.constraint_type * Id.t Loc.located) list -> unit

(** {6 Hooks for Pcoq} *)

val set_declare_definition_hook : (definition_entry -> unit) -> unit
val get_declare_definition_hook : unit -> (definition_entry -> unit)

(** {6 Definitions/Let} *)

val interp_definition :
  local_binder list -> polymorphic -> red_expr option -> constr_expr ->
  constr_expr option -> definition_entry * Evd.evar_map * Impargs.manual_implicits

val declare_definition : Id.t -> definition_kind ->
  definition_entry -> Impargs.manual_implicits ->
    Globnames.global_reference Lemmas.declaration_hook -> Globnames.global_reference

val do_definition : Id.t -> definition_kind ->
  local_binder list -> red_expr option -> constr_expr ->
  constr_expr option -> unit Lemmas.declaration_hook -> unit

(** {6 Parameters/Assumptions} *)

(* val interp_assumption : env -> evar_map ref -> *)
(*   local_binder list -> constr_expr ->  *)
(*   types Univ.in_universe_context_set * Impargs.manual_implicits *)

(** returns [false] if the assumption is neither local to a section,
    nor in a module type and meant to be instantiated. *)
val declare_assumption : coercion_flag -> assumption_kind -> 
  types Univ.in_universe_context_set ->
  Impargs.manual_implicits ->
  bool (** implicit *) -> Vernacexpr.inline -> variable Loc.located ->
  global_reference * Univ.Instance.t * bool

val do_assumptions : locality * polymorphic * assumption_object_kind ->
  Vernacexpr.inline -> simple_binder with_coercion list -> bool

(* val declare_assumptions : variable Loc.located list -> *)
(*   coercion_flag -> assumption_kind -> types Univ.in_universe_context_set ->  *)
(*   Impargs.manual_implicits -> bool -> Vernacexpr.inline -> bool *)

(** {6 Inductive and coinductive types} *)

(** Extracting the semantical components out of the raw syntax of mutual
   inductive declarations *)

type structured_one_inductive_expr = {
  ind_name : Id.t;
  ind_arity : constr_expr;
  ind_lc : (Id.t * constr_expr) list
}

type structured_inductive_expr =
  local_binder list * structured_one_inductive_expr list

val extract_mutual_inductive_declaration_components :
  (one_inductive_expr * decl_notation list) list ->
    structured_inductive_expr * (*coercions:*) qualid list * decl_notation list

(** Typing mutual inductive definitions *)

type one_inductive_impls =
  Impargs.manual_implicits (** for inds *)*
  Impargs.manual_implicits list (** for constrs *)

val interp_mutual_inductive :
  structured_inductive_expr -> decl_notation list -> polymorphic ->
    private_flag -> Decl_kinds.recursivity_kind ->
    mutual_inductive_entry * one_inductive_impls list

(** Registering a mutual inductive definition together with its
   associated schemes *)

val declare_mutual_inductive_with_eliminations :
  mutual_inductive_entry -> one_inductive_impls list ->
  mutual_inductive

(** Entry points for the vernacular commands Inductive and CoInductive *)

val do_mutual_inductive :
  (one_inductive_expr * decl_notation list) list -> polymorphic -> 
  private_flag -> Decl_kinds.recursivity_kind -> unit

(** {6 Fixpoints and cofixpoints} *)

type structured_fixpoint_expr = {
  fix_name : Id.t;
  fix_annot : Id.t Loc.located option;
  fix_binders : local_binder list;
  fix_body : constr_expr option;
  fix_type : constr_expr
}

(** Extracting the semantical components out of the raw syntax of
   (co)fixpoints declarations *)

val extract_fixpoint_components : bool ->
  (fixpoint_expr * decl_notation list) list ->
    structured_fixpoint_expr list * decl_notation list

val extract_cofixpoint_components :
  (cofixpoint_expr * decl_notation list) list ->
    structured_fixpoint_expr list * decl_notation list

(** Typing global fixpoints and cofixpoint_expr *)

type recursive_preentry =
  Id.t list * constr option list * types list

val interp_fixpoint :
  structured_fixpoint_expr list -> decl_notation list ->
    recursive_preentry * Evd.evar_universe_context * 
    (Name.t list * Impargs.manual_implicits * int option) list

val interp_cofixpoint :
  structured_fixpoint_expr list -> decl_notation list ->
    recursive_preentry * Evd.evar_universe_context * 
    (Name.t list * Impargs.manual_implicits * int option) list

(** Registering fixpoints and cofixpoints in the environment *)

val declare_fixpoint :
  locality -> polymorphic ->
  recursive_preentry * Evd.evar_universe_context * 
  (Name.t list * Impargs.manual_implicits * int option) list ->
  lemma_possible_guards -> decl_notation list -> unit

val declare_cofixpoint : locality -> polymorphic -> 
  recursive_preentry * Evd.evar_universe_context * 
  (Name.t list * Impargs.manual_implicits * int option) list ->
  decl_notation list -> unit

(** Entry points for the vernacular commands Fixpoint and CoFixpoint *)

val do_fixpoint :
  locality -> polymorphic -> (fixpoint_expr * decl_notation list) list -> unit

val do_cofixpoint :
  locality -> polymorphic -> (cofixpoint_expr * decl_notation list) list -> unit

(** Utils *)

val check_mutuality : Environ.env -> bool -> (Id.t * types) list -> unit

val declare_fix : definition_kind -> Univ.universe_context -> Id.t ->
  Entries.proof_output -> types -> Impargs.manual_implicits -> global_reference
