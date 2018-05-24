(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Entry point for generic printers *)

open Genarg

type 'a with_level =
  { default_already_surrounded : Notation_gram.tolerability;
    default_ensure_surrounded : Notation_gram.tolerability;
    printer : 'a }

type printer_result =
| PrinterBasic of (unit -> Pp.t)
| PrinterNeedsLevel of (Notation_gram.tolerability -> Pp.t) with_level

type printer_fun_with_level = Environ.env -> Evd.evar_map -> Notation_gram.tolerability -> Pp.t

type top_printer_result =
| TopPrinterBasic of (unit -> Pp.t)
| TopPrinterNeedsContext of (Environ.env -> Evd.evar_map -> Pp.t)
| TopPrinterNeedsContextAndLevel of printer_fun_with_level with_level

type 'a printer = 'a -> printer_result

type 'a top_printer = 'a -> top_printer_result

val raw_print : ('raw, 'glb, 'top) genarg_type -> 'raw printer
(** Printer for raw level generic arguments. *)

val glb_print : ('raw, 'glb, 'top) genarg_type -> 'glb printer
(** Printer for glob level generic arguments. *)

val top_print : ('raw, 'glb, 'top) genarg_type -> 'top top_printer
(** Printer for top level generic arguments. *)

val register_print0 : ('raw, 'glb, 'top) genarg_type ->
  'raw printer -> 'glb printer -> 'top top_printer -> unit
val register_val_print0 : 'top Geninterp.Val.typ ->
  'top top_printer -> unit
val register_vernac_print0 : ('raw, 'glb, 'top) genarg_type ->
  'raw printer -> unit

val generic_raw_print : rlevel generic_argument printer
val generic_glb_print : glevel generic_argument printer
val generic_top_print : tlevel generic_argument top_printer
val generic_val_print : Geninterp.Val.t top_printer
