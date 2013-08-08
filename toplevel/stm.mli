(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Add a transaction (an edit that adds a new line to the script).
   The bool is there for -compile-verbose *)
val process_transaction : bool -> Vernacexpr.located_vernac_expr -> unit

(* Evaluates the tip of the current branch *)
val finish : unit -> unit

(* Evaluates a particular state id (does not move the current tip) *)
val observe : Stateid.state_id -> unit

(* Joins the entire document.  Implies finish, but also checks proofs *)
val join : unit -> unit

val get_current_state : unit -> Stateid.state_id
val current_proof_depth : unit -> int
val get_all_proof_names : unit -> Names.identifier list
val get_current_proof_name : unit -> Names.identifier option

val init : unit -> unit
val slave_main_loop : unit -> unit
val slave_init_stdout : unit -> unit
