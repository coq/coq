(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Ssrast

val pp_term :
  Goal.goal Evd.sigma -> EConstr.constr -> Pp.std_ppcmds

val pr_spc : unit -> Pp.std_ppcmds
val pr_bar : unit -> Pp.std_ppcmds
val pr_list : 
  (unit -> Pp.std_ppcmds) -> ('a -> Pp.std_ppcmds) -> 'a list -> Pp.std_ppcmds

val pp_concat :
  Pp.std_ppcmds ->
  ?sep:Pp.std_ppcmds -> Pp.std_ppcmds list -> Pp.std_ppcmds

val xInParens : ssrtermkind
val xWithAt : ssrtermkind
val xNoFlag : ssrtermkind
val xCpattern : ssrtermkind

val pr_term :
  ssrtermkind * (Glob_term.glob_constr * Constrexpr.constr_expr option) ->
  Pp.std_ppcmds

val pr_hyp : ssrhyp -> Pp.std_ppcmds

val prl_constr_expr : Constrexpr.constr_expr -> Pp.std_ppcmds
val prl_glob_constr : Glob_term.glob_constr -> Pp.std_ppcmds

val pr_guarded :
  (string -> int -> bool) -> ('a -> Pp.std_ppcmds) -> 'a -> Pp.std_ppcmds

val pr_occ : ssrocc -> Pp.std_ppcmds

val ppdebug : Pp.std_ppcmds Lazy.t -> unit

