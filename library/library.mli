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
val require_library_from_dirpath : (DirPath.t * string) list -> bool option -> unit
val require_library_from_file :
  Id.t option -> CUnix.physical_path -> bool option -> unit

(** {6 ... } *)
(** Open a module (or a library); if the boolean is true then it's also
   an export otherwise just a simple import *)
val import_module : bool -> qualid located -> unit

(** {6 Start the compilation of a library } *)
val start_library : string -> DirPath.t * string

(** {6 End the compilation of a library and save it to a ".vo" file } *)
val save_library_to : ?todo:'a -> DirPath.t -> string -> unit
val load_library_todo : string -> 'a * string

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

(** {6 Hook for the xml exportation of libraries } *)
val xml_require : (DirPath.t -> unit) Hook.t

(** {6 Locate a library in the load paths } *)
exception LibUnmappedDir
exception LibNotFound
type library_location = LibLoaded | LibInPath

val locate_qualified_library :
  bool -> qualid -> library_location * DirPath.t * CUnix.physical_path
val try_locate_qualified_library : qualid located -> DirPath.t * string

(** {6 Statistics: display the memory use of a library. } *)
val mem : DirPath.t -> Pp.std_ppcmds
