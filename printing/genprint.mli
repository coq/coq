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

type 'a printer_without_level = 'a -> std_ppcmds
type 'a printer_with_level = Ppextend.tolerability -> 'a -> std_ppcmds
type 'a printer = Ppextend.tolerability option -> 'a -> std_ppcmds

val raw_print : ('raw, 'glb, 'top) genarg_type -> 'raw printer
(** Printer for raw level generic arguments. *)

val glb_print : ('raw, 'glb, 'top) genarg_type -> 'glb printer
(** Printer for glob level generic arguments. *)

val top_print : ('raw, 'glb, 'top) genarg_type -> 'top printer
(** Printer for top level generic arguments. *)

val generic_raw_print : rlevel generic_argument printer
val generic_glb_print : glevel generic_argument printer
val generic_top_print : tlevel generic_argument printer

val register_print0 : ('raw, 'glb, 'top) genarg_type ->
  'raw printer_without_level -> 'glb printer_without_level -> 'top printer_without_level -> unit

val register_print_with_level0 : ('raw, 'glb, 'top) genarg_type ->
  'raw printer_with_level -> 'glb printer_with_level -> 'top printer_with_level -> unit
