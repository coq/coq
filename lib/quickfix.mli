(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t

val make : loc:Loc.t -> Pp.t -> t

val pp : t -> Pp.t

val loc : t -> Loc.t

(** [register h] registers [h] as a quickfix generator.
    When an error is generated the toplevel can check if there is
    quick fix for it.

    Quickfix generators signal that they don't deal with some exception
    by returning []. Raising any other exception is
    forbidden.

    Exceptions that are considered anomalies should not be
    handled by Quickfix generators.
*)

val register : (exn -> t list) -> unit

(** computes all the quickfixes for a given exception *)
val from_exception : exn -> (t list, Exninfo.iexn) result

(** Prints all the quickfixes in a vertical box *)
val print : t list -> Pp.t
