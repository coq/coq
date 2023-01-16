(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Tac2expr
open Tac2ffi

(** {5 Printing types} *)

type typ_level =
| T5_l
| T5_r
| T2
| T1
| T0

val pr_typref : type_constant -> Pp.t
val pr_glbtype_gen : ('a -> string) -> typ_level -> 'a glb_typexpr -> Pp.t
val pr_glbtype : ('a -> string) -> 'a glb_typexpr -> Pp.t

(** {5 Printing expressions} *)

val pr_constructor : ltac_constructor -> Pp.t
val pr_internal_constructor : type_constant -> int -> bool -> Pp.t
val pr_projection : ltac_projection -> Pp.t
val pr_glbexpr_gen : exp_level -> glb_tacexpr -> Pp.t
val pr_glbexpr : glb_tacexpr -> Pp.t
val pr_partial_pat : PartialPat.t -> Pp.t

(** Utility function *)
val partial_pat_of_glb_pat : glb_pat -> PartialPat.t

(** {5 Printing values}*)

type val_printer =
  { val_printer : 'a. Environ.env -> Evd.evar_map -> valexpr -> 'a glb_typexpr list -> Pp.t }

val register_val_printer : type_constant -> val_printer -> unit

val pr_valexpr : Environ.env -> Evd.evar_map -> valexpr -> 'a glb_typexpr -> Pp.t

(** {5 Utilities} *)

val int_name : unit -> (int -> string)
(** Create a function that give names to integers. The names are generated on
    the fly, in the order they are encountered. *)

(** {5 Ltac2 primitives}*)

type format =
| FmtString
| FmtInt
| FmtConstr
| FmtIdent
| FmtLiteral of string
| FmtAlpha

val format : format list Tac2ffi.repr

exception InvalidFormat

val parse_format : string -> format list
