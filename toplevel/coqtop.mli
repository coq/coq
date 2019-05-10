(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Definition of custom toplevels.
    [init] is used to do custom command line argument parsing.
    [run] launches a custom toplevel.
*)

type 'a extra_args_fn = opts:Coqargs.t -> string list -> 'a * string list

type ('a,'b) custom_toplevel =
  { parse_extra : 'a extra_args_fn
  ; help : Usage.specific_usage
  ; init : 'a -> opts:Coqargs.t -> 'b
  ; run : 'a -> opts:Coqargs.t -> 'b -> unit
  ; opts : Coqargs.t
  }

(** The generic Coq main module. [start custom] will parse the command line,
   print the banner, initialize the load path, load the input state,
   load the files given on the command line, load the resource file,
   produce the output state if any, and finally will launch
   [custom.run]. *)
val start_coq : ('a,'b) custom_toplevel -> unit

(** Initializer color for output *)

val init_color : Coqargs.coqargs_config -> unit

(** Prepare state for interactive loop *)

val init_toploop : Coqargs.t -> Vernac.State.t

(** The specific characterization of the coqtop_toplevel *)

type run_mode = Interactive | Batch

val coqtop_toplevel : (run_mode,Vernac.State.t) custom_toplevel
