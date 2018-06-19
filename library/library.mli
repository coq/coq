(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Libnames

(** This module provides functions to load, open and save
  libraries. Libraries correspond to the subclass of modules that
  coincide with a file on disk (the ".vo" files). Libraries on the
  disk comes with checksums (obtained with the [Digest] module), which
  are checked at loading time to prevent inconsistencies between files
  written at various dates.
*)

(** {6 ... } *)
(** Require = load in the environment + open (if the optional boolean
    is not [None]); mark also for export if the boolean is [Some true] *)
val require_library_from_dirpath : (DirPath.t * string) list -> bool option -> unit

(** {6 Start the compilation of a library } *)

(** Segments of a library *)
type seg_sum
type seg_lib
type seg_univ = (* cst, all_cst, finished? *)
  Univ.ContextSet.t Future.computation array * Univ.ContextSet.t * bool
type seg_discharge = Opaqueproof.cooking_info list array
type seg_proofs = Constr.constr Future.computation array

(** Open a module (or a library); if the boolean is true then it's also
   an export otherwise just a simple import *)
val import_module : bool -> qualid list -> unit

(** Start the compilation of a file as a library. The first argument must be
    output file, and the 
    returned path is the associated absolute logical path of the library. *)
val start_library : CUnix.physical_path -> DirPath.t

(** End the compilation of a library and save it to a ".vo" file *)
val save_library_to :
  ?todo:(((Future.UUID.t,'document) Stateid.request * bool) list * 'counters) ->
  DirPath.t -> string -> Opaqueproof.opaquetab -> unit

val load_library_todo :
  string -> string * seg_sum * seg_lib * seg_univ * seg_discharge * 'tasks * seg_proofs
val save_library_raw : string -> seg_sum -> seg_lib -> seg_univ -> seg_proofs -> unit

(** {6 Interrogate the status of libraries } *)

  (** - Tell if a library is loaded or opened *)
val library_is_loaded : DirPath.t -> bool
val library_is_opened : DirPath.t -> bool

  (** - Tell which libraries are loaded or imported *)
val loaded_libraries : unit -> DirPath.t list
val opened_libraries : unit -> DirPath.t list

  (** - Return the full filename of a loaded library. *)
val library_full_filename : DirPath.t -> string

  (** - Overwrite the filename of all libraries (used when restoring a state) *)
val overwrite_library_filenames : string -> unit

(** {6 Locate a library in the load paths } *)
exception LibUnmappedDir
exception LibNotFound
type library_location = LibLoaded | LibInPath

val locate_qualified_library :
  ?root:DirPath.t -> ?warn:bool -> qualid ->
  library_location * DirPath.t * CUnix.physical_path
(** Locates a library by implicit name.

  @raise LibUnmappedDir if the library is not in the path
  @raise LibNotFound if there is no corresponding file in the path

*)

(** {6 Native compiler. } *)
val native_name_from_filename : string -> string
