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

(*s This module is the heart of the library. It provides low level
  functions to load, open and save libraries. Libraries are saved
  onto the disk with checksums (obtained with the [Digest] module),
  which are checked at loading time to prevent inconsistencies
  between files written at various dates. It also provides a high
  level function [require] which corresponds to the vernacular
  command [Require]. *)

val read_library : qualid located -> unit

val read_library_from_file : System.physical_path -> unit

(* [import_library true qid] = [export qid] *)
 
val import_library : bool -> qualid located -> unit

val library_is_loaded : dir_path -> bool
val library_is_opened : dir_path -> bool

val loaded_libraries : unit -> dir_path list
val opened_libraries : unit -> dir_path list

val fmt_libraries_state : unit -> Pp.std_ppcmds

(*s Require. The command [require_library spec m file export] loads and opens
  a library [m]. [file] specifies the filename, if not [None]. [spec]
  specifies to look for a specification ([true]) or for an implementation
  ([false]), if not [None]. And [export] specifies if the library must be 
  exported. *)

val require_library :
  bool option -> qualid located list -> bool -> unit

val require_library_from_file :
  bool option -> identifier option -> System.physical_path -> bool -> unit

val set_xml_require : (dir_path -> unit) -> unit

(*s [save_library_to s f] saves the current environment as a library [s]
  in the file [f]. *)

val start_library : string -> dir_path * string
val save_library_to : dir_path -> string -> unit

(* [library_full_filename] returns the full filename of a loaded library. *)

val library_full_filename : dir_path -> string


(*s Global load path *)
type logical_path = dir_path

val get_load_path : unit -> System.physical_path list
val get_full_load_path : unit -> (System.physical_path * logical_path) list
val add_load_path_entry : System.physical_path * logical_path -> unit
val remove_path : System.physical_path -> unit
val find_logical_path : System.physical_path -> logical_path
val load_path_of_logical_path : dir_path -> System.physical_path list

exception LibUnmappedDir
exception LibNotFound
type library_location = LibLoaded | LibInPath

val locate_qualified_library :
  qualid -> library_location * dir_path * System.physical_path


val check_required_library : string list -> unit

(*s Displays the memory use of a library. *)
val mem : dir_path -> Pp.std_ppcmds

(* For discharge *)
type library_reference

val out_require : Libobject.obj -> library_reference
val reload_library : library_reference -> unit
