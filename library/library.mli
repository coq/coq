(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Libobject
(*i*)

(*s This module is the heart of the library. It provides low level functions to
   load, open and save modules. Modules are saved onto the disk with checksums
   (obtained with the [Digest] module), which are checked at loading time to
   prevent inconsistencies between files written at various dates. It also
   provides a high level function [require] which corresponds to the 
   vernacular command [Require]. *)

val read_module : Nametab.qualid -> unit
val read_module_from_file : System.physical_path -> unit
val import_module : bool -> Nametab.qualid -> unit

val module_is_loaded : dir_path -> bool
val module_is_opened : dir_path -> bool

val loaded_modules : unit -> dir_path list
val opened_modules : unit -> dir_path list

val fmt_modules_state : unit -> Pp.std_ppcmds

(*s Require. The command [require_module spec m file export] loads and opens
  a module [m]. [file] specifies the filename, if not [None]. [spec]
  specifies to look for a specification ([true]) or for an implementation
  ([false]), if not [None]. And [export] specifies if the module must be 
  exported. *)

val require_module :
  bool option -> Nametab.qualid list -> bool -> unit

val require_module_from_file :
  bool option -> Nametab.qualid -> string -> bool -> unit

(*s [save_module_to s f] saves the current environment as a module [s]
  in the file [f]. *)

val save_module_to : dir_path -> string -> unit

(*s [module_segment m] returns the segment of the loaded module
    [m]; if not given, the segment of the current module is returned
    (which is then the same as [Lib.contents_after None]). 
    [module_full_filename] returns the full filename of a loaded module. *)

val module_segment : dir_path option -> Lib.library_segment
val module_full_filename : dir_path -> string

(*s [fold_all_segments] and [iter_all_segments] iterate over all
    segments, the modules' segments first and then the current
    segment. Modules are presented in an arbitrary order. The given
    function is applied to all leaves (together with their section
    path). The boolean indicates if we must enter closed sections. *)

val fold_all_segments : bool -> ('a -> section_path -> obj -> 'a) -> 'a -> 'a
val iter_all_segments : bool -> (section_path -> obj -> unit) -> unit

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
  Nametab.qualid -> library_location * dir_path * System.physical_path

(*s Displays the memory use of a module. *)

val mem : dir_path -> Pp.std_ppcmds

(* For discharge *)
type module_reference

val out_require : Libobject.obj -> module_reference
val reload_module : module_reference -> unit
