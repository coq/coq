(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file provides facilities to access OCaml compiler and dynamic linker,
used by the native compiler. *)

(* Directory where compiled files are stored *)
val output_dir : CUnix.physical_path ref
val include_dirs : CUnix.physical_path list ref

val get_load_paths : (unit -> string list) ref

val load_obj : (string -> unit) ref

val get_ml_filename : unit -> string * string

(** [compile file code ~profile] will compile native [code] to [file],
   and return the name of the object file; this name depends on
   whether are in byte mode or not; file is expected to be .ml file *)
val compile : string -> Nativecode.global list -> profile:bool -> string

type native_library = Nativecode.global list * Nativevalues.symbols

(** [compile_library (code, _) file] is similar to [compile file code]
   but will perform some extra tweaks to handle [code] as a Coq lib. *)
val compile_library : native_library -> string -> unit

(** [execute_library file upds] dynamically loads library [file],
    updates the library locations [upds], and returns the values stored
    in [rt1] and [rt2] *)
val execute_library :
  prefix:string -> string -> Nativecode.code_location_updates ->
  Nativevalues.t * Nativevalues.t

(** [enable_library] marks the given library for dynamic loading
    the next time [link_libraries] is called. *)
val enable_library : string -> Names.DirPath.t -> unit

val link_libraries : unit -> unit

(* used for communication with the loaded libraries *)
val rt1 : Nativevalues.t ref
val rt2 : Nativevalues.t ref
