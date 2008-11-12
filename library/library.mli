(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Libnames
open Libobject
(*i*)

(*s This module provides functions to load, open and save
  libraries. Libraries correspond to the subclass of modules that
  coincide with a file on disk (the ".vo" files). Libraries on the
  disk comes with checksums (obtained with the [Digest] module), which
  are checked at loading time to prevent inconsistencies between files
  written at various dates.
*)

(*s Require = load in the environment + open (if the optional boolean
    is not [None]); mark also for export if the boolean is [Some true] *)
val require_library : qualid located list -> bool option -> unit
val require_library_from_file :
  identifier option -> System.physical_path -> bool option -> unit

(*s Open a module (or a library); if the boolean is true then it's also
   an export otherwise just a simple import *)
val import_module : bool -> qualid located -> unit

(*s Start the compilation of a library *)
val start_library : string -> dir_path * string

(*s End the compilation of a library and save it to a ".vo" file *)
val save_library_to : dir_path -> string -> unit

(*s Interrogate the status of libraries *)

  (* - Tell if a library is loaded or opened *)
val library_is_loaded : dir_path -> bool
val library_is_opened : dir_path -> bool

  (* - Tell which libraries are loaded or imported *)
val loaded_libraries : unit -> dir_path list
val opened_libraries : unit -> dir_path list

  (* - Return the full filename of a loaded library. *)
val library_full_filename : dir_path -> string

  (* - Overwrite the filename of all libraries (used when restoring a state) *)
val overwrite_library_filenames : string -> unit

(*s Hook for the xml exportation of libraries *)
val set_xml_require : (dir_path -> unit) -> unit

(*s Global load paths: a load path is a physical path in the file
    system; to each load path is associated a Coq [dir_path] (the "logical"
    path of the physical path) *)

val get_load_paths : unit -> System.physical_path list
val get_full_load_paths : unit -> (System.physical_path * dir_path) list
val add_load_path : bool -> System.physical_path * dir_path -> unit
val remove_load_path : System.physical_path -> unit
val find_logical_path : System.physical_path -> dir_path
val is_in_load_paths : System.physical_path -> bool

(*s Locate a library in the load paths *)
exception LibUnmappedDir
exception LibNotFound
type library_location = LibLoaded | LibInPath

val locate_qualified_library :
  bool -> qualid -> library_location * dir_path * System.physical_path
val try_locate_qualified_library : qualid located -> dir_path * string

(*s Statistics: display the memory use of a library. *)
val mem : dir_path -> Pp.std_ppcmds
