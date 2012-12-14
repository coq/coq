(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Pp
open Names
open Libnames
open Libobject

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
val require_library : qualid located list -> bool option -> unit
val require_library_from_dirpath : (Dir_path.t * string) list -> bool option -> unit
val require_library_from_file :
  Id.t option -> CUnix.physical_path -> bool option -> unit

(** {6 ... } *)
(** Open a module (or a library); if the boolean is true then it's also
   an export otherwise just a simple import *)
val import_module : bool -> qualid located -> unit

(** {6 Start the compilation of a library } *)
val start_library : string -> Dir_path.t * string

(** {6 End the compilation of a library and save it to a ".vo" file } *)
val save_library_to : Dir_path.t -> string -> unit

(** {6 Interrogate the status of libraries } *)

  (** - Tell if a library is loaded or opened *)
val library_is_loaded : Dir_path.t -> bool
val library_is_opened : Dir_path.t -> bool

  (** - Tell which libraries are loaded or imported *)
val loaded_libraries : unit -> Dir_path.t list
val opened_libraries : unit -> Dir_path.t list

  (** - Return the full filename of a loaded library. *)
val library_full_filename : Dir_path.t -> string

  (** - Overwrite the filename of all libraries (used when restoring a state) *)
val overwrite_library_filenames : string -> unit

(** {6 Hook for the xml exportation of libraries } *)
val set_xml_require : (Dir_path.t -> unit) -> unit

(** {6 ... } *)
(** Global load paths: a load path is a physical path in the file
    system; to each load path is associated a Coq [Dir_path.t] (the "logical"
    path of the physical path) *)

val get_load_paths : unit -> CUnix.physical_path list
val get_full_load_paths : unit -> (CUnix.physical_path * Dir_path.t) list
val add_load_path : bool -> CUnix.physical_path * Dir_path.t -> unit
val remove_load_path : CUnix.physical_path -> unit
val find_logical_path : CUnix.physical_path -> Dir_path.t
val is_in_load_paths : CUnix.physical_path -> bool

(** {6 Locate a library in the load paths } *)
exception LibUnmappedDir
exception LibNotFound
type library_location = LibLoaded | LibInPath

val locate_qualified_library :
  bool -> qualid -> library_location * Dir_path.t * CUnix.physical_path
val try_locate_qualified_library : qualid located -> Dir_path.t * string

(** {6 Statistics: display the memory use of a library. } *)
val mem : Dir_path.t -> Pp.std_ppcmds
