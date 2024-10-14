(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This is about warnings triggered from user .v code ("warn" attibute).
    See cWarnings.mli for the generic warning interface. *)

type warn = private { note : string; cats : string }
(** note and comma separated list of categories *)

type t = { depr : Deprecation.t option; warn : warn list }
type 'a with_qf = { depr_qf : 'a Deprecation.with_qf option; warn_qf : warn list }

val drop_qf : 'a with_qf -> t
val with_empty_qf : t -> 'a with_qf

val empty : t

val make_warn : note:string -> ?cats:string -> unit -> warn

val create_warning : ?default:CWarnings.status -> warning_name_if_no_cats:string ->
  unit -> ?loc:Loc.t -> warn -> unit

val create_depr_and_user_warnings : ?default:CWarnings.status ->
  object_name:string -> warning_name_base:string ->
  ('a -> Pp.t) -> unit ->
  ?loc:Loc.t -> 'a -> t -> unit
