(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Parsing of vernacular. *)

(** [process_expr sid cmd] Executes vernac command [cmd]. Callers are
    expected to handle and print errors in form of exceptions, however
    care is taken so the state machine is left in a consistent
    state. *)
val process_expr : Stm.doc -> Stateid.t -> Vernacexpr.vernac_expr Loc.located -> Stm.doc * Stateid.t

(** [load_vernac echo sid file] Loads [file] on top of [sid], will
    echo the commands if [echo] is set. Callers are expected to handle
    and print errors in form of exceptions. *)
val load_vernac : verbosely:bool -> check:bool -> interactive:bool -> Stm.doc -> Stateid.t -> string -> Stm.doc * Stateid.t

type compilation_mode = BuildVo | BuildVio | Vio2Vo

(** Compile a vernac file, (f is assumed without .v suffix) *)
val compile : verbosely:bool -> mode:compilation_mode -> doc:Stm.doc -> f_in:string -> f_out:string option -> unit
