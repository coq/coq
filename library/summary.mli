
(*i $Id$ i*)

(*i*)
open Names
(*i*)

(* This module registers the declaration of global tables, which will be kept
   in synchronization during the various backtracks of the system. *)

type 'a summary_declaration = {
  freeze_function : unit -> 'a;
  unfreeze_function : 'a -> unit;
  init_function : unit -> unit;
  survive_section : bool }

val declare_summary : string -> 'a summary_declaration -> unit

type frozen

val freeze_summaries : unit -> frozen
val unfreeze_summaries : frozen -> unit
val unfreeze_lost_summaries : frozen -> unit
val init_summaries : unit -> unit



