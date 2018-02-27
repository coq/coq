(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Remote counters are *global* counters for fresh ids.  In the master/slave
 * scenario, the slave installs a getter that asks the master for a fresh
 * value.  In the scenario of a slave that runs after the death of the master
 * on some marshalled data, a backup of all counters status should be taken and
 * restored to avoid reusing ids.
 * Counters cannot be created by threads, they must be created once and forall
 * as toplevel module declarations. *)


type 'a getter = unit -> 'a
type 'a installer = ('a getter) -> unit

val new_counter : name:string ->
  'a -> incr:('a -> 'a) -> build:('a -> 'b) -> 'b getter * 'b installer

type remote_counters_status
val backup : unit -> remote_counters_status
(* like backup but makes a copy so that further increment does not alter
 * the snapshot *)
val snapshot : unit -> remote_counters_status
val restore : remote_counters_status -> unit
