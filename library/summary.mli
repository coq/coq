(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(* This module registers the declaration of global tables, which will be kept
   in synchronization during the various backtracks of the system. *)

type 'a summary_declaration = {
  freeze_function : unit -> 'a;
  unfreeze_function : 'a -> unit;
  init_function : unit -> unit }

val declare_summary : string -> 'a summary_declaration -> unit

type frozen

val freeze_summaries : unit -> frozen
val unfreeze_summaries : frozen -> unit
val init_summaries : unit -> unit

(** Beware: if some code is dynamically loaded via dynlink after the
    initialization of Coq, the init functions of any summary declared
    by this code may not be run. It is hence the responsability of
    plugins to initialize themselves properly.
*)

