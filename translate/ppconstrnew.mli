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
open Extend
open Coqast
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
val pr_binders : local_binder list -> std_ppcmds

val prec_less : int -> int * Ppextend.parenRelation -> bool
 
val pr_global : Idset.t -> global_reference -> std_ppcmds
 
val pr_tight_coma : unit -> std_ppcmds
val pr_located :
  ('a -> std_ppcmds) -> 'a located -> std_ppcmds
val pr_lident : identifier located -> std_ppcmds
val pr_lname : name located -> std_ppcmds

val pr_with_comments : loc -> std_ppcmds -> std_ppcmds
val pr_com_at : int -> std_ppcmds
val pr_sep_com :
  (unit -> std_ppcmds) ->
  (constr_expr -> std_ppcmds) ->
  constr_expr -> std_ppcmds
val pr_opt : ('a -> std_ppcmds) -> 'a option -> std_ppcmds
val pr_id : identifier -> std_ppcmds
val pr_name : name -> std_ppcmds
val pr_qualid : qualid -> std_ppcmds
val pr_or_var : ('a -> std_ppcmds) -> 'a or_var -> std_ppcmds
val pr_metaid : identifier -> std_ppcmds
val pr_red_expr :
  ('a -> std_ppcmds) * ('a -> std_ppcmds) *  ('b -> std_ppcmds) ->
    ('a,'b) red_expr_gen -> std_ppcmds

val pr_sort : rawsort -> std_ppcmds
val pr_pattern : Tacexpr.pattern_expr -> std_ppcmds
val pr_constr : constr_expr -> std_ppcmds
val pr_lconstr : constr_expr -> std_ppcmds
val pr_constr_env : env -> constr_expr -> std_ppcmds
val pr_lconstr_env : env -> constr_expr -> std_ppcmds
val pr_lconstr_env_n : env -> bool -> local_binder list -> constr_expr -> 
  local_binder list * std_ppcmds
val pr_type_env_n : env -> local_binder list -> constr_expr -> std_ppcmds
val pr_type : constr_expr -> std_ppcmds
val pr_cases_pattern : cases_pattern_expr -> std_ppcmds
val pr_may_eval :
  ('a -> std_ppcmds) -> ('a -> std_ppcmds) -> ('b -> std_ppcmds) -> ('a,'b) may_eval
    -> std_ppcmds
val abstract_constr_expr : constr_expr -> local_binder list -> constr_expr
val prod_constr_expr : constr_expr -> local_binder list -> constr_expr


val pr_rawconstr_env : env -> rawconstr -> std_ppcmds
val pr_lrawconstr_env : env -> rawconstr -> std_ppcmds

val pr_rawconstr_env_no_translate : env -> rawconstr -> std_ppcmds
val pr_lrawconstr_env_no_translate : env -> rawconstr -> std_ppcmds

val pr_reference : reference -> std_ppcmds

(** constr printers *)

val pr_term_env : env -> constr -> std_ppcmds
val pr_lterm_env : env -> constr -> std_ppcmds
val pr_term : constr -> std_ppcmds
val pr_lterm : constr -> std_ppcmds

val pr_constr_pattern_env : env -> Pattern.constr_pattern -> std_ppcmds
val pr_constr_pattern : Pattern.constr_pattern -> std_ppcmds

(* To translate names in ZArith *)
val translate_with_bindings : rawconstr -> 'a bindings -> 'a bindings
val rename_bound_variables : identifier -> constr_expr -> constr_expr
