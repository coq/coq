
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
 
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

val pr_located : ('a -> std_ppcmds) -> 'a located -> std_ppcmds
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
  ('a -> std_ppcmds) * ('a -> std_ppcmds) * ('b -> std_ppcmds) ->
    ('a,'b) red_expr_gen -> std_ppcmds
val pr_may_eval :
  ('a -> std_ppcmds) -> ('a -> std_ppcmds) -> ('b -> std_ppcmds) -> 
    ('a,'b) may_eval -> std_ppcmds

val pr_rawsort : rawsort -> std_ppcmds

val pr_binders : local_binder list -> std_ppcmds
val pr_pattern_expr : Tacexpr.pattern_expr -> std_ppcmds
val pr_lpattern_expr : Tacexpr.pattern_expr -> std_ppcmds
val pr_constr_expr : constr_expr -> std_ppcmds
val pr_lconstr_expr : constr_expr -> std_ppcmds
val pr_cases_pattern_expr : cases_pattern_expr -> std_ppcmds
