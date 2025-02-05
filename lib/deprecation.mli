(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t = { since : string option ; note : string option }
type 'a with_qf = { depr : t; use_instead : 'a option }

val drop_qf : 'a with_qf -> t
val with_empty_qf : t -> 'a with_qf

val make : ?since:string -> ?note:string -> unit -> t
val make_with_qf : ?since:string -> ?note:string -> ?use_instead:'qf -> unit -> 'qf with_qf

val create_warning : ?default:CWarnings.status -> object_name:string -> warning_name_if_no_since:string ->
  ('b -> Pp.t) -> ?loc:Loc.t -> 'b * t -> unit
val create_warning_with_qf : ?default:CWarnings.status -> object_name:string -> warning_name_if_no_since:string ->
  pp_qf:('qf -> Pp.t) -> ('b -> Pp.t) -> ?loc:Loc.t -> 'b * 'qf with_qf -> unit

module Version : sig
  val v8_3 : CWarnings.category
  val v8_5 : CWarnings.category
  val v8_8 : CWarnings.category
  val v8_10 : CWarnings.category
  val v8_11 : CWarnings.category
  val v8_14 : CWarnings.category
  val v8_15 : CWarnings.category
  val v8_16 : CWarnings.category
  val v8_17 : CWarnings.category
  val v8_18 : CWarnings.category
  val v8_19 : CWarnings.category
  val v8_20 : CWarnings.category
  val v9_0 : CWarnings.category
  val v9_1 : CWarnings.category
end
