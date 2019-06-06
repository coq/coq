(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Nativecode

(** This file provides facilities to access OCaml compiler and dynamic linker,
used by the native compiler. *)

(* Directory where compiled files are stored *)
val output_dir : string

val get_load_paths : (unit -> string list) ref

val load_obj : (string -> unit) ref

val get_ml_filename : unit -> string * string

(** [compile file code ~profile] will compile native [code] to [file],
   and return the name of the object file; this name depends on
   whether are in byte mode or not; file is expected to be .ml file *)
val compile : string -> global list -> profile:bool -> string

(** [compile_library lib code file] is similar to [compile file code]
   but will perform some extra tweaks to handle [code] as a Coq lib. *)
val compile_library : Names.DirPath.t -> global list -> string -> unit

val call_linker :
  ?fatal:bool -> string -> string -> code_location_updates option -> unit

val link_library : prefix:string -> dirname:string -> basename:string -> unit

val rt1 : Nativevalues.t ref
val rt2 : Nativevalues.t ref
