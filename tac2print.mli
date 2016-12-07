(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Names
open Tac2expr

(** {5 Printing types} *)

val pr_typref : type_constant -> std_ppcmds
val pr_glbtype : ('a -> string) -> 'a glb_typexpr -> std_ppcmds

(** {5 Printing expressions} *)

val pr_constructor : ltac_constructor -> std_ppcmds
val pr_projection : ltac_projection -> std_ppcmds
val pr_glbexpr : glb_tacexpr -> std_ppcmds

(** {5 Utilities} *)

val int_name : unit -> (int -> string)
(** Create a function that give names to integers. The names are generated on
    the fly, in the order they are encountered. *)
