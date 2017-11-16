(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module implements pretty-printers for constr_expr syntactic
    objects and their subcomponents. *)

(** The default pretty-printers produce pretty-printing commands ({!Pp.t}). *)
open Loc
open Libnames
open Constrexpr
open Names
open Misctypes
open Notation_term

val extract_lam_binders :
  constr_expr -> local_binder_expr list * constr_expr
val extract_prod_binders :
  constr_expr -> local_binder_expr list * constr_expr
val split_fix :
  int -> constr_expr -> constr_expr ->
  local_binder_expr list *  constr_expr * constr_expr

val prec_less : precedence -> tolerability -> bool

val pr_tight_coma : unit -> Pp.t

val pr_or_var : ('a -> Pp.t) -> 'a or_var -> Pp.t

val pr_lident : Id.t located -> Pp.t
val pr_lname : Name.t located -> Pp.t

val pr_with_comments : ?loc:Loc.t -> Pp.t -> Pp.t
val pr_com_at : int -> Pp.t
val pr_sep_com :
  (unit -> Pp.t) ->
  (constr_expr -> Pp.t) ->
  constr_expr -> Pp.t

val pr_id : Id.t -> Pp.t
val pr_name : Name.t -> Pp.t
[@@ocaml.deprecated "alias of Names.Name.print"]

val pr_qualid : qualid -> Pp.t
val pr_patvar : patvar -> Pp.t

val pr_glob_level : glob_level -> Pp.t
val pr_glob_sort : glob_sort -> Pp.t
val pr_guard_annot : (constr_expr -> Pp.t) ->
  local_binder_expr list ->
  ('a * Names.Id.t) option * recursion_order_expr ->
  Pp.t

val pr_record_body : (reference * constr_expr) list -> Pp.t
val pr_binders : local_binder_expr list -> Pp.t
val pr_constr_pattern_expr : constr_pattern_expr -> Pp.t
val pr_lconstr_pattern_expr : constr_pattern_expr -> Pp.t
val pr_constr_expr : constr_expr -> Pp.t
val pr_lconstr_expr : constr_expr -> Pp.t
val pr_cases_pattern_expr : cases_pattern_expr -> Pp.t
val pr_constr_expr_n : tolerability -> constr_expr -> Pp.t

type term_pr = {
  pr_constr_expr   : constr_expr -> Pp.t;
  pr_lconstr_expr  : constr_expr -> Pp.t;
  pr_constr_pattern_expr  : constr_pattern_expr -> Pp.t;
  pr_lconstr_pattern_expr : constr_pattern_expr -> Pp.t
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

val lsimpleconstr : tolerability
val ltop : tolerability
val modular_constr_pr :
  ((unit->Pp.t) -> tolerability -> constr_expr -> Pp.t) ->
  (unit->Pp.t) -> tolerability -> constr_expr -> Pp.t
