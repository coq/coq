(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Vernacexpr
open Interface
open Names

(** state-transaction-machine interface *)

(* [add ontop check vebose eid s] adds a new command [s] on the state [ontop]
   having edit id [eid].  [check] is called on the AST.
   The [ontop] parameter is just for asserting the GUI is on sync, but
   will eventually call edit_at on the fly if needed.
   The sentence [s] is parsed in the state [ontop]. *)
val add : ontop:Stateid.t -> ?check:(located_vernac_expr -> unit) ->
  bool -> edit_id -> string ->
    Stateid.t * [ `NewTip | `Unfocus of Stateid.t ]

(* parses and xecutes a command at a given state, throws away its side effects
   but for the printings *)
val query : at:Stateid.t -> string -> unit

(* [edit_at id] is issued to change the editing zone.  [`NewTip] is returned if
   the requested id is the new document tip hence the document portion following
   [id] is dropped by Coq.  [`Focus fo] is returned to say that [fo.tip] is the
   new document tip, the document between [id] and [fo.stop] has been dropped.
   The portion between [fo.stop] and [fo.tip] has been kept.  [fo.start] is
   just to tell the gui where the editing zone starts, in case it wants to
   graphically denote it.  All subsequent [add] happen on top of [id]. *)
type focus = { start : Stateid.t; stop : Stateid.t; tip : Stateid.t }
val edit_at : Stateid.t -> [ `NewTip | `Focus of focus ]

(* Evaluates the tip of the current branch *)
val finish : unit -> unit

(* Joins the entire document.  Implies finish, but also checks proofs *)
val join : unit -> unit
(* To save to disk an incomplete document *)
type tasks
val dump : unit -> tasks

(* Id of the tip of the current branch *)
val get_current_state : unit -> Stateid.t

(* Misc *)
val init : unit -> unit
val slave_main_loop : unit -> unit
val slave_init_stdout : unit -> unit

val set_compilation_hints : Aux_file.aux_file -> unit

(** read-eval-print loop compatible interface ****************************** **)

(* Adds a new line to the document.  It replaces the core of Vernac.interp.
   [finish] is called as the last bit of this function is the system
   is running interactively (-emacs or coqtop). *)
val interp : bool -> located_vernac_expr -> unit

(* Queries for backward compatibility *)
val current_proof_depth : unit -> int
val get_all_proof_names : unit -> Id.t list
val get_current_proof_name : unit -> Id.t option

