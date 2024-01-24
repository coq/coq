(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val query_command :
  (Goal_select.t option -> Vernacexpr.synpure_vernac_expr) Pcoq.Entry.t

val search_query : (bool * Vernacexpr.search_request) Pcoq.Entry.t

val search_queries :
  ((bool * Vernacexpr.search_request) list * Libnames.qualid list Vernacexpr.search_restriction)
    Pcoq.Entry.t

val subprf : Vernacexpr.synpure_vernac_expr Pcoq.Entry.t

val quoted_attributes : Attributes.vernac_flags Pcoq.Entry.t

val coercion_class : Vernacexpr.coercion_class Pcoq.Entry.t

val thm_token : Decls.theorem_kind Pcoq.Entry.t

val def_token :
  (Vernacexpr.discharge * Decls.definition_object_kind) Pcoq.Entry.t

val assumption_token :
  (Vernacexpr.discharge * Decls.assumption_object_kind) Pcoq.Entry.t

val def_body : Vernacexpr.definition_expr Pcoq.Entry.t

val notation_declaration : Vernacexpr.notation_declaration Pcoq.Entry.t

val decl_notations : Vernacexpr.notation_declaration list Pcoq.Entry.t

val record_field :
  (Vernacexpr.local_decl_expr * Vernacexpr.record_field_attr_unparsed) Pcoq.Entry.t

val of_type : Vernacexpr.coercion_flag Pcoq.Entry.t

val of_type_inst :
  (Vernacexpr.coercion_flag * Vernacexpr.instance_flag) Pcoq.Entry.t

val section_subset_expr : Vernacexpr.section_subset_expr Pcoq.Entry.t

val scope_delimiter : Vernacexpr.scope_delimiter Pcoq.Entry.t

val syntax_modifiers : Vernacexpr.syntax_modifier CAst.t list Pcoq.Entry.t

val make_bullet : string -> Proof_bullet.t

val test_hash_ident : unit Pcoq.Entry.t

val test_id_colon : unit Pcoq.Entry.t

val warn_plural_command : ?loc:Loc.t -> string -> unit

val test_variance_ident : unit Pcoq.Entry.t

val test_only_starredidentrefs : unit Pcoq.Entry.t

val goal_selector : Goal_select.t Pcoq.Entry.t

val toplevel_selector : Goal_select.t Pcoq.Entry.t
