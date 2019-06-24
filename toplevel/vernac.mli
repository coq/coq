(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Parsing of vernacular. *)
module State : sig

  type t = {
    doc : Stm.doc;
    sid : Stateid.t;
    proof : Proof.t option;
    time : bool;
  }

end


(** [checknav_simple ctrl] Throws an error if the current command
    in the AST is a navigation command. *)
val checknav_simple : Vernacexpr.vernac_control -> unit

(** [process_expr sid cmd] Executes vernac command [cmd]. Callers are
    expected to handle and print errors in form of exceptions, however
    care is taken so the state machine is left in a consistent
    state. *)
val process_expr : state:State.t -> Vernacexpr.vernac_control -> State.t

(** [load_vernac echo sid file] Loads [file] on top of [sid], will
    echo the commands if [echo] is set. Callers are expected to handle
    and print errors in form of exceptions. *)
val load_vernac : echo:bool -> check:bool -> interactive:bool ->
  state:State.t -> string -> State.t

(** [interp_vernac check interactive sid ctrl] Interprets the current
    command in the AST and this way sets the state given by [sid] to
    a new state. If [check] is set, the stm will check the execution.
    If [interactive] is set, the underlying document of the AST [ast]
    is edited. *)
val interp_vernac : check:bool -> interactive:bool -> state:State.t ->
  Vernacexpr.vernac_control -> State.t
