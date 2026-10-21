(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module implements pretty-printers for constr_expr syntactic
    objects and their subcomponents. *)

(** The default pretty-printers produce pretty-printing commands ({!Pp.t}). *)
open Libnames
open Constrexpr
open Names

type flags = { parentheses : bool }

val current_flags : unit -> flags
val of_extern_flags : PrintingFlags.Extern.t -> flags
val of_printing_flags : PrintingFlags.t -> flags

val pr_tight_coma : unit -> Pp.t

val pr_with_comments : ?loc:Loc.t -> Pp.t -> Pp.t
val pr_com_at : int -> Pp.t
val pr_sep_com :
  (unit -> Pp.t) ->
  (constr_expr -> Pp.t) ->
  constr_expr -> Pp.t

val pr_id : Id.t -> Pp.t

val pr_qualid : qualid -> Pp.t
val pr_patvar : Pattern.patvar -> Pp.t

val pr_sort_name_expr : sort_name_expr -> Pp.t
val pr_sort_expr : sort_expr -> Pp.t
val pr_quality_expr : quality_expr -> Pp.t
val pr_guard_annot
  :  (constr_expr -> Pp.t)
  -> local_binder_expr list
  -> fixpoint_order_expr option
  -> Pp.t

val pr_record : string -> string -> Pp.t option -> ('a -> Pp.t) -> 'a list -> Pp.t
val pr_record_body : string -> string -> ('a -> Pp.t) -> Pp.t option -> (Libnames.qualid * 'a) list -> Pp.t
val pr_binders : flags:flags -> Environ.env -> Evd.evar_map -> local_binder_expr list -> Pp.t
val pr_constr_pattern_expr : flags:flags -> Environ.env -> Evd.evar_map -> constr_pattern_expr -> Pp.t
val pr_lconstr_pattern_expr : flags:flags -> Environ.env -> Evd.evar_map -> constr_pattern_expr -> Pp.t
val pr_constr_expr : flags:flags -> Environ.env -> Evd.evar_map -> constr_expr -> Pp.t
val pr_lconstr_expr : flags:flags -> Environ.env -> Evd.evar_map -> constr_expr -> Pp.t
val pr_cases_pattern_expr : flags:flags -> cases_pattern_expr -> Pp.t
val pr_constr_expr_n : flags:flags -> Environ.env -> Evd.evar_map -> entry_relative_level -> constr_expr -> Pp.t

type term_pr = {
  pr_constr_expr : flags:flags -> Environ.env -> Evd.evar_map -> constr_expr -> Pp.t;
  pr_lconstr_expr : flags:flags -> Environ.env -> Evd.evar_map -> constr_expr -> Pp.t;
  pr_constr_pattern_expr : flags:flags -> Environ.env -> Evd.evar_map -> constr_pattern_expr -> Pp.t;
  pr_lconstr_pattern_expr : flags:flags -> Environ.env -> Evd.evar_map -> constr_pattern_expr -> Pp.t
}

val set_term_pr : term_pr -> unit
val default_term_pr : term_pr

(* The modular constr printer.
  [modular_constr_pr pr s p t] prints the head of the term [t] and calls
  [pr] on its subterms.
  [s] is typically {!Pp.mt} and [p] is [lsimpleconstr] for "constr" printers
  and [ltop] for "lconstr" printers (spiwack: we might need more
  specification here).
  We can make a new modular constr printer by overriding certain branches,
  for instance if we want to build a printer which prints "Prop" as "Omega"
  instead we can proceed as follows:
  let my_modular_constr_pr pr s p = function
  | CSort (_,GProp Null) -> str "Omega"
  | t -> modular_constr_pr pr s p t
  Which has the same type. We can turn a modular printer into a printer by
  taking its fixpoint. *)

val lsimpleconstr : entry_relative_level
val ltop : entry_relative_level

(* Print at level "simpleconstr"  (applications are surrounded with parentheses)
   ensured not to be overriden, on the contrary of pr_constr_expr *)
val pr_simpleconstr : flags:flags -> constr_expr -> Pp.t

(* Print at level "top" (no parentheses)
   ensured not to be overriden, on the contrary of pr_lconstr_expr *)
val pr_top : flags:flags -> constr_expr -> Pp.t

val modular_constr_pr :
  flags:flags ->
  ((unit->Pp.t) -> int option -> entry_relative_level -> constr_expr -> Pp.t) ->
  (unit->Pp.t) -> int option -> entry_relative_level -> constr_expr -> Pp.t

module CompactedDecl : sig
  type t =
    | LocalAssum of (Environ.var_status option * Id.t EConstr.binder_annot) list * EConstr.types
    | LocalDef of (Environ.var_status option * Id.t EConstr.binder_annot) list * EConstr.constr * EConstr.types

  val of_named_decl : Environ.var_status option -> EConstr.named_declaration -> t

  val to_tuple : t ->
    Id.t EConstr.binder_annot list *
    EConstr.constr option *
    EConstr.types
end

val compact_named_context : Evd.evar_map -> Environ.named_context_val -> CompactedDecl.t list
