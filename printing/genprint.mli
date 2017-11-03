(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Entry point for generic printers *)

open Genarg

type printer_with_level =
  { default_already_surrounded : Notation_term.tolerability;
    default_ensure_surrounded : Notation_term.tolerability;
    printer : Environ.env -> Evd.evar_map -> Notation_term.tolerability -> Pp.t }

type printer_result =
| PrinterBasic of (unit -> Pp.t)
| PrinterNeedsContext of (Environ.env -> Evd.evar_map -> Pp.t)
| PrinterNeedsContextAndLevel of printer_with_level

type 'a printer = 'a -> Pp.t

type 'a top_printer = 'a -> printer_result

val raw_print : ('raw, 'glb, 'top) genarg_type -> 'raw printer
(** Printer for raw level generic arguments. *)

val glb_print : ('raw, 'glb, 'top) genarg_type -> 'glb printer
(** Printer for glob level generic arguments. *)

val top_print : ('raw, 'glb, 'top) genarg_type -> 'top top_printer
(** Printer for top level generic arguments. *)

val register_print0 : ('raw, 'glb, 'top) genarg_type ->
  'raw printer -> 'glb printer -> ('top -> printer_result) -> unit
val register_val_print0 : 'top Geninterp.Val.typ ->
  'top top_printer -> unit
val register_vernac_print0 : ('raw, 'glb, 'top) genarg_type ->
  'raw printer -> unit

val generic_raw_print : rlevel generic_argument printer
val generic_glb_print : glevel generic_argument printer
val generic_top_print : tlevel generic_argument top_printer
val generic_val_print : Geninterp.Val.t top_printer
