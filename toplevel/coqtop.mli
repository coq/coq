(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Definition of custom toplevels.
    [init_extra] is used to do custom initialization
    [run] launches a custom toplevel.
*)

type ('a,'b) custom_toplevel =
  { parse_extra : Coqargs.t -> string list -> 'a * string list
  ; usage : Boot.Usage.specific_usage
  ; init_extra : 'a -> Coqargs.injection_command list -> opts:Coqargs.t -> 'b
  ; initial_args : Coqargs.t
  ; run : 'a -> opts:Coqargs.t -> 'b -> unit
  }

(** The generic Rocq main module. [start custom] will parse the command line,
   print the banner, initialize the load path, load the input state,
   load the files given on the command line, load the resource file,
   produce the output state if any, and finally will launch
   [custom.run].

    The [string list] argument is typically [List.tl (Array.to_list Sys.argv)].
*)
val start_coq : ('a * Stm.AsyncOpts.stm_opt,'b) custom_toplevel -> string list -> unit

(** Prepare state for interactive loop *)

val init_toploop : Coqargs.t -> Stm.AsyncOpts.stm_opt -> Coqargs.injection_command list -> Vernac.State.t

(** The specific characterization of the coqtop_toplevel *)

type query = PrintTags | PrintModUid of string list
type run_mode = Interactive | Batch | Query of query

type toplevel_options = {
  run_mode : run_mode;
  color_mode : Colors.color;
}

val coqtop_toplevel : (toplevel_options * Stm.AsyncOpts.stm_opt,Vernac.State.t) custom_toplevel

val ltac_debug_answer : DebugHook.Answer.t -> unit

val ltac_debug_parse : unit -> DebugHook.Action.t
