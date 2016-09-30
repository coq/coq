(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Entry point for generic printers *)

open Pp
open Genarg

type 'a printer = 'a -> std_ppcmds

val raw_print : ('raw, 'glb, 'top) genarg_type -> 'raw -> std_ppcmds
(** Printer for raw level generic arguments. *)

val glb_print : ('raw, 'glb, 'top) genarg_type -> 'glb -> std_ppcmds
(** Printer for glob level generic arguments. *)

val top_print : ('raw, 'glb, 'top) genarg_type -> 'top -> std_ppcmds
(** Printer for top level generic arguments. *)

val generic_raw_print : rlevel generic_argument printer
val generic_glb_print : glevel generic_argument printer
val generic_top_print : tlevel generic_argument printer

val register_print0 : ('raw, 'glb, 'top) genarg_type ->
  'raw printer -> 'glb printer -> 'top printer -> unit
