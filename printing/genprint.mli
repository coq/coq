(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Entry point for generic printers *)

open Genarg

type 'a with_level =
  { default_already_surrounded : Constrexpr.entry_relative_level;
    default_ensure_surrounded : Constrexpr.entry_relative_level;
    printer : 'a }

type printer_result =
| PrinterBasic of (Environ.env -> Evd.evar_map -> Pp.t)
| PrinterNeedsLevel of (Environ.env -> Evd.evar_map -> Constrexpr.entry_relative_level -> Pp.t) with_level

type printer_fun_with_level = Environ.env -> Evd.evar_map -> Constrexpr.entry_relative_level -> Pp.t

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
(** The genarg must be registered in [Geninterp.register_val0] *)

val register_noval_print0 : ('raw, 'glb, Util.Empty.t) genarg_type ->
  'raw printer -> 'glb printer -> unit
val register_val_print0 : 'top Geninterp.Val.typ ->
  'top top_printer -> unit
val register_vernac_print0 : 'raw vernac_genarg_type ->
  'raw printer -> unit

val generic_raw_print : rlevel generic_argument printer
val generic_glb_print : glevel generic_argument printer
val generic_top_print : tlevel generic_argument top_printer
val generic_val_print : Geninterp.Val.t top_printer
