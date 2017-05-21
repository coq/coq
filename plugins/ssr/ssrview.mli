(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Ssrast
open Ssrcommon

val viewtab : Glob_term.glob_constr list array
val add_view_hints : Glob_term.glob_constr list -> int -> unit
val glob_view_hints : Constrexpr.constr_expr list -> Glob_term.glob_constr list

val pfa_with_view :
           ist ->
           ?next:ssripats ref ->
           bool * ssrterm list ->
           EConstr.t ->
           EConstr.t ->
           (EConstr.t -> EConstr.t -> tac_ctx tac_a) ->
           ssrhyps ->
   (goal * tac_ctx) sigma -> EConstr.types * EConstr.t * (goal * tac_ctx) list sigma

val pf_with_view_linear :
           ist ->
           goal sigma ->
           bool * ssrterm list ->
           EConstr.t ->
           EConstr.t ->
           EConstr.types * EConstr.t * goal sigma


