(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Initialization. *)

val set_debug : unit -> unit

val load_rcfile : rcfile:(string option) -> time:bool -> state:Vernac.State.t -> Vernac.State.t

val init_ocaml_path : unit -> unit

(* LoadPath for toploop toplevels *)
val toplevel_init_load_path : unit ->  Mltop.coq_path list

(* LoadPath for Coq user libraries *)
val libs_init_load_path : load_init:bool -> Mltop.coq_path list

(** [get_version] returns the version and branch strings *)
val get_version : unit -> string * string
