(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Parsing of vernacular. *)
module State : sig

  type t = {
    doc : Stm.doc;
    sid : Stateid.t;
    proof : Proof.t option;
  }

end

(** [process_expr sid cmd] Executes vernac command [cmd]. Callers are
    expected to handle and print errors in form of exceptions, however
    care is taken so the state machine is left in a consistent
    state. *)
val process_expr : time:bool -> state:State.t -> Vernacexpr.vernac_control Loc.located -> State.t

(** [load_vernac echo sid file] Loads [file] on top of [sid], will
    echo the commands if [echo] is set. Callers are expected to handle
    and print errors in form of exceptions. *)
val load_vernac : time:bool -> verbosely:bool -> check:bool -> interactive:bool ->
  state:State.t -> string -> State.t
