
(* $Id$ *)

(*i*)
open Names
(*i*)

(* This module registers the declaration of global tables, which will be kept
   in synchronization during the various backtracks of the system. *)

type 'a summary_declaration = {
  freeze_function : unit -> 'a;
  unfreeze_function : 'a -> unit;
  init_function : unit -> unit }

val declare_summary : string -> 'a summary_declaration -> unit

type frozen_summaries

val freeze_summaries : unit -> frozen_summaries
val unfreeze_summaries : frozen_summaries -> unit
val init_summaries : unit -> unit



