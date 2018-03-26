(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Initialization. *)

val set_debug : unit -> unit

val load_rcfile : rcfile:(string option) -> state:Vernac.State.t -> Vernac.State.t

val init_ocaml_path : unit -> unit

(* LoadPath for toploop toplevels *)
val toplevel_init_load_path : unit -> Mltop.coq_path list

(* LoadPath for Coq user libraries *)
val libs_init_load_path : load_init:bool -> Mltop.coq_path list
