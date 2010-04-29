
(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(*i $Id$ i*)

open Pp
open Environ
open Term
open Libnames
open Pcoq
open Rawterm
open Topconstr
open Names
open Util
open Genarg

val extract_lam_binders :
  constr_expr -> local_binder list * constr_expr
val extract_prod_binders :
  constr_expr -> local_binder list * constr_expr
val extract_def_binders :
  constr_expr -> constr_expr ->
  local_binder list * constr_expr * constr_expr
val split_fix :
  int -> constr_expr -> constr_expr ->
  local_binder list *  constr_expr * constr_expr

val prec_less : int -> int * Ppextend.parenRelation -> bool

val pr_tight_coma : unit -> std_ppcmds

val pr_or_var : ('a -> std_ppcmds) -> 'a or_var -> std_ppcmds
val pr_metaid : identifier -> std_ppcmds

val pr_lident : identifier located -> std_ppcmds
val pr_lname : name located -> std_ppcmds

val pr_with_comments : loc -> std_ppcmds -> std_ppcmds
val pr_com_at : int -> std_ppcmds
val pr_sep_com :
  (unit -> std_ppcmds) ->
  (constr_expr -> std_ppcmds) ->
  constr_expr -> std_ppcmds

val pr_id : identifier -> std_ppcmds
val pr_name : name -> std_ppcmds
val pr_qualid : qualid -> std_ppcmds

val pr_with_occurrences :
  ('a -> std_ppcmds) -> 'a with_occurrences -> std_ppcmds
val pr_red_expr :
  ('a -> std_ppcmds) * ('a -> std_ppcmds) * ('b -> std_ppcmds) * ('c -> std_ppcmds) ->
    ('a,'b,'c) red_expr_gen -> std_ppcmds
val pr_may_eval :
  ('a -> std_ppcmds) -> ('a -> std_ppcmds) -> ('b -> std_ppcmds) ->
  ('c -> std_ppcmds) -> ('a,'b,'c) may_eval -> std_ppcmds

val pr_rawsort : rawsort -> std_ppcmds

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
    [s] is typically {!Pp.mt} and [p] is [lsimple] for "constr" printers and [ltop]
    for "lconstr" printers (spiwack: we might need more specification here).
    We can make a new modular constr printer by overriding certain branches,
    for instance if we want to build a printer which prints "Prop" as "Omega"
    instead we can proceed as follows:
    let my_modular_constr_pr pr s p = function
      | CSort (_,RProp Null) -> str "Omega"
      | t -> modular_constr_pr pr s p t
    Which has the same type. We can turn a modular printer into a printer by
    taking its fixpoint. *)

type precedence
val lsimple : precedence
val ltop : precedence
val modular_constr_pr :
               ((unit->std_ppcmds) -> precedence -> constr_expr -> std_ppcmds) ->
                (unit->std_ppcmds) -> precedence  -> constr_expr -> std_ppcmds
