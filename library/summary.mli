(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
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
  init_function : unit -> unit;
  survive_module : bool;    (* should be false is most cases *)
  survive_section : bool }

val declare_summary : string -> 'a summary_declaration -> unit

type frozen

val freeze_summaries : unit -> frozen
val unfreeze_summaries : frozen -> unit
val section_unfreeze_summaries : frozen -> unit
val module_unfreeze_summaries : frozen -> unit
val init_summaries : unit -> unit



