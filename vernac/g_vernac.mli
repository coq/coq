(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val query_command :
  (Goal_select.t option -> Vernacexpr.synpure_vernac_expr) Procq.Entry.t

val search_query : (bool * Vernacexpr.search_request) Procq.Entry.t

val search_queries :
  ((bool * Vernacexpr.search_request) list * Libnames.qualid list Vernacexpr.search_restriction)
    Procq.Entry.t

val subprf : Vernacexpr.synpure_vernac_expr Procq.Entry.t
val subprf_with_selector : (Goal_select.t option -> Vernacexpr.synpure_vernac_expr) Procq.Entry.t

val quoted_attributes : Attributes.vernac_flags Procq.Entry.t

val coercion_class : Vernacexpr.coercion_class Procq.Entry.t

val thm_token : Decls.theorem_kind Procq.Entry.t

val def_token :
  (Vernacexpr.discharge * Decls.definition_object_kind) Procq.Entry.t

val assumption_token :
  (Vernacexpr.discharge * Decls.assumption_object_kind) Procq.Entry.t

val def_body : Vernacexpr.definition_expr Procq.Entry.t

val notation_declaration : Vernacexpr.notation_declaration Procq.Entry.t

val decl_notations : Vernacexpr.notation_declaration list Procq.Entry.t

val record_field :
  (Vernacexpr.local_decl_expr * Vernacexpr.record_field_attr_unparsed) Procq.Entry.t

val of_type : Vernacexpr.coercion_flag Procq.Entry.t

val of_type_inst :
  (Vernacexpr.coercion_flag * Vernacexpr.instance_flag) Procq.Entry.t

val section_subset_expr : Vernacexpr.section_subset_expr Procq.Entry.t

val scope_delimiter : Vernacexpr.scope_delimiter Procq.Entry.t

val syntax_modifiers : Vernacexpr.syntax_modifier CAst.t list Procq.Entry.t

val make_bullet : string -> Proof_bullet.t

val test_hash_ident : unit Procq.Entry.t

val test_id_colon : unit Procq.Entry.t

val warn_plural_command : ?loc:Loc.t -> string -> unit

val test_variance_ident : unit Procq.Entry.t

val test_only_starredidentrefs : unit Procq.Entry.t

val goal_selector : Goal_select.t Procq.Entry.t

val toplevel_selector : Goal_select.t Procq.Entry.t
