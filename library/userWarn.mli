(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

val empty : t

val make_warn : note:string -> ?cats:string -> unit -> warn

val create_warning : ?default:CWarnings.status -> warning_name_if_no_cats:string ->
  unit -> ?loc:Loc.t -> warn -> unit
