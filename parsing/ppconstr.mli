(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

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

val split_fix : int -> constr_expr -> constr_expr -> 
  (name located list * constr_expr) list * constr_expr * constr_expr

val pr_global : Idset.t -> global_reference -> std_ppcmds

val pr_opt : ('a -> std_ppcmds) -> 'a option -> std_ppcmds
val pr_name : name -> std_ppcmds
val pr_qualid : qualid -> std_ppcmds
val pr_red_expr :
  ('a -> std_ppcmds) * ('b -> std_ppcmds) ->
    ('a,'b) red_expr_gen -> std_ppcmds
val pr_occurrences : ('a -> std_ppcmds) -> 'a occurrences -> std_ppcmds

val pr_sort : rawsort -> std_ppcmds
val pr_pattern : Tacexpr.pattern_expr -> std_ppcmds
val pr_constr : constr_expr -> std_ppcmds
val pr_cases_pattern : cases_pattern_expr -> std_ppcmds
val pr_may_eval : ('a -> std_ppcmds) -> ('b -> std_ppcmds) -> ('a,'b) may_eval -> std_ppcmds
val pr_rawconstr : rawconstr -> std_ppcmds
