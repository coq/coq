(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Parsing of vernacular. *)

(** Reads and executes vernac commands from a stream. *)
val process_expr : Stateid.t -> Pcoq.Gram.coq_parsable -> Vernacexpr.vernac_expr Loc.located -> Stateid.t

(** [load_vernac echo sid file] Loads [file] on top of [sid], will
    echo the commands if [echo] is set. *)
val load_vernac : bool -> Stateid.t -> string -> Stateid.t

(** Compile a vernac file, (f is assumed without .v suffix) *)
val compile : bool -> string -> unit

(** Set XML hooks *)
val xml_start_library : (unit -> unit) Hook.t
val xml_end_library   : (unit -> unit) Hook.t
