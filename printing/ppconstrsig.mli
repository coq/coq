(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Pp
open Libnames
open Constrexpr
open Names
open Misctypes
open Locus
open Genredexpr

module type Pp = sig

  val extract_lam_binders :
    constr_expr -> local_binder list * constr_expr
  val extract_prod_binders :
    constr_expr -> local_binder list * constr_expr
  val split_fix :
    int -> constr_expr -> constr_expr ->
    local_binder list *  constr_expr * constr_expr

  val prec_less : int -> int * Ppextend.parenRelation -> bool

  val pr_tight_coma : unit -> std_ppcmds

  val pr_or_var : ('a -> std_ppcmds) -> 'a or_var -> std_ppcmds

  val pr_lident : Id.t located -> std_ppcmds
  val pr_lname : Name.t located -> std_ppcmds

  val pr_with_comments : Loc.t -> std_ppcmds -> std_ppcmds
  val pr_com_at : int -> std_ppcmds
  val pr_sep_com :
    (unit -> std_ppcmds) ->
    (constr_expr -> std_ppcmds) ->
    constr_expr -> std_ppcmds

  val pr_id : Id.t -> std_ppcmds
  val pr_name : Name.t -> std_ppcmds
  val pr_qualid : qualid -> std_ppcmds
  val pr_patvar : patvar -> std_ppcmds

  val pr_glob_sort : glob_sort -> std_ppcmds
  val pr_guard_annot : (constr_expr -> std_ppcmds) ->
    local_binder list ->
    ('a * Names.Id.t) option * recursion_order_expr ->
    std_ppcmds

  val pr_binders : local_binder list -> std_ppcmds
  val pr_constr_pattern_expr : constr_pattern_expr -> std_ppcmds
  val pr_lconstr_pattern_expr : constr_pattern_expr -> std_ppcmds
  val pr_constr_expr : constr_expr -> std_ppcmds
  val pr_lconstr_expr : constr_expr -> std_ppcmds
  val pr_cases_pattern_expr : cases_pattern_expr -> std_ppcmds

  type term_pr = {
    pr_constr_expr   : constr_expr -> std_ppcmds;
    pr_lconstr_expr  : constr_expr -> std_ppcmds;
    pr_constr_pattern_expr  : constr_pattern_expr -> std_ppcmds;
    pr_lconstr_pattern_expr : constr_pattern_expr -> std_ppcmds
  }

  val set_term_pr : term_pr -> unit
  val default_term_pr : term_pr

(** The modular constr printer.
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

  type precedence
  val lsimpleconstr : precedence
  val ltop : precedence
  val modular_constr_pr :
    ((unit->std_ppcmds) -> precedence -> constr_expr -> std_ppcmds) ->
    (unit->std_ppcmds) -> precedence  -> constr_expr -> std_ppcmds

end

