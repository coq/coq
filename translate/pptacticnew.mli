(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
 
(* $Id$ *)

open Pp
open Genarg
open Tacexpr
open Proof_type
open Topconstr
open Names

val qsnew : string -> std_ppcmds

val pr_intro_pattern : intro_pattern_expr -> std_ppcmds

val pr_raw_tactic : Environ.env -> raw_tactic_expr -> std_ppcmds
 
val pr_glob_tactic : Environ.env -> glob_tactic_expr -> std_ppcmds

val pr_tactic : Environ.env -> Proof_type.tactic_expr -> std_ppcmds

val id_of_ltac_v7_id : identifier -> identifier


