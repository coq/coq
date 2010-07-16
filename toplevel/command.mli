(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Term
open Entries
open Libnames
open Tacexpr
open Vernacexpr
open Topconstr
open Decl_kinds
open Redexpr
open Constrintern
open Pfedit

(** This file is about the interpretation of raw commands into typed
    ones and top-level declaration of the main Gallina objects *)

(** {6 Hooks for Pcoq} *)

val set_declare_definition_hook : (definition_entry -> unit) -> unit
val get_declare_definition_hook : unit -> (definition_entry -> unit)
val set_declare_assumptions_hook : (types -> unit) -> unit

(** {6 Definitions/Let} *)

val interp_definition :
  boxed_flag -> local_binder list -> red_expr option -> constr_expr ->
  constr_expr option -> definition_entry * manual_implicits

val declare_definition : identifier -> locality * definition_object_kind ->
  definition_entry -> manual_implicits -> declaration_hook -> unit

(** {6 Parameters/Assumptions} *)

val interp_assumption :
  local_binder list -> constr_expr -> types * manual_implicits

val declare_assumption : coercion_flag -> assumption_kind -> types ->
  manual_implicits ->
  bool (** implicit *) -> bool (* inline *) -> variable located -> unit

val declare_assumptions : variable located list ->
  coercion_flag -> assumption_kind -> types -> manual_implicits ->
  bool -> bool -> unit

(** {6 Inductive and coinductive types} *)

(** Extracting the semantical components out of the raw syntax of mutual
   inductive declarations *)

type structured_one_inductive_expr = {
  ind_name : identifier;
  ind_arity : constr_expr;
  ind_lc : (identifier * constr_expr) list
}

type structured_inductive_expr =
  local_binder list * structured_one_inductive_expr list

val extract_mutual_inductive_declaration_components :
  (one_inductive_expr * decl_notation list) list ->
    structured_inductive_expr * (*coercions:*) qualid list * decl_notation list

(** Typing mutual inductive definitions *)

type one_inductive_impls =
  Impargs.manual_explicitation list (** for inds *)*
  Impargs.manual_explicitation list list (** for constrs *)

val interp_mutual_inductive :
  structured_inductive_expr -> decl_notation list -> bool ->
    mutual_inductive_entry * one_inductive_impls list

(** Registering a mutual inductive definition together with its
   associated schemes *)

val declare_mutual_inductive_with_eliminations :
  Declare.internal_flag -> mutual_inductive_entry -> one_inductive_impls list ->
  mutual_inductive

(** Entry points for the vernacular commands Inductive and CoInductive *)

val do_mutual_inductive :
  (one_inductive_expr * decl_notation list) list -> bool -> unit

(** {6 Fixpoints and cofixpoints} *)

type structured_fixpoint_expr = {
  fix_name : identifier;
  fix_annot : identifier located option;
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
  identifier list * constr option list * types list

val interp_fixpoint :
  structured_fixpoint_expr list -> decl_notation list ->
    recursive_preentry * (name list * manual_implicits * int option) list

val interp_cofixpoint :
  structured_fixpoint_expr list -> decl_notation list ->
    recursive_preentry * (name list * manual_implicits * int option) list

(** Registering fixpoints and cofixpoints in the environment *)

val declare_fixpoint :
  bool ->
  recursive_preentry * (name list * manual_implicits * int option) list -> 
  lemma_possible_guards -> decl_notation list -> unit

val declare_cofixpoint :
  bool ->
  recursive_preentry * (name list * manual_implicits * int option) list ->
    decl_notation list -> unit

(** Entry points for the vernacular commands Fixpoint and CoFixpoint *)

val do_fixpoint :
  (fixpoint_expr * decl_notation list) list -> bool -> unit

val do_cofixpoint :
  (cofixpoint_expr * decl_notation list) list -> bool -> unit

(** Utils *)

val check_mutuality : Environ.env -> bool -> (identifier * types) list -> unit

val declare_fix : bool -> definition_object_kind -> identifier ->
  constr -> types -> Impargs.manual_explicitation list -> global_reference
