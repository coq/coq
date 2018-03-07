(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
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
type custom_toplevel = {
  init : opts:Coqargs.coq_cmdopts -> string list -> Coqargs.coq_cmdopts * string list;
  run  : opts:Coqargs.coq_cmdopts -> state:Vernac.State.t -> unit;
}

val coqtop_toplevel : custom_toplevel

(** The Coq main module. [start custom] will parse the command line,
   print the banner, initialize the load path, load the input state,
   load the files given on the command line, load the resource file,
   produce the output state if any, and finally will launch
   [custom.run]. *)

val start_coq : custom_toplevel -> unit
