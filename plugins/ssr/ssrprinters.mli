(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Ssrast

val pp_term :
  Goal.goal Evd.sigma -> EConstr.constr -> Pp.t

val pr_spc : unit -> Pp.t
val pr_bar : unit -> Pp.t
val pr_list : 
  (unit -> Pp.t) -> ('a -> Pp.t) -> 'a list -> Pp.t

val pp_concat :
  Pp.t ->
  ?sep:Pp.t -> Pp.t list -> Pp.t

val xInParens : ssrtermkind
val xWithAt : ssrtermkind
val xNoFlag : ssrtermkind
val xCpattern : ssrtermkind

val pr_term :
  ssrtermkind * (Glob_term.glob_constr * Constrexpr.constr_expr option) ->
  Pp.t

val pr_hyp : ssrhyp -> Pp.t

val prl_constr_expr : Constrexpr.constr_expr -> Pp.t
val prl_glob_constr : Glob_term.glob_constr -> Pp.t

val pr_guarded :
  (string -> int -> bool) -> ('a -> Pp.t) -> 'a -> Pp.t

val pr_occ : ssrocc -> Pp.t

val ppdebug : Pp.t Lazy.t -> unit

