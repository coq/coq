
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

val load_module : string -> string option -> unit
val import_module : string -> unit

val module_is_loaded : string -> bool
val module_is_opened : string -> bool

val loaded_modules : unit -> string list
val opened_modules : unit -> string list

val fmt_modules_state : unit -> Pp.std_ppcmds

(*s Require. The command [require_module spec m file export] loads and opens
  a module [m]. [file] specifies the filename, if not [None]. [spec]
  specifies to look for a specification ([true]) or for an implementation
  ([false]), if not [None]. And [export] specifies if the module must be 
  exported. *)

val require_module : bool option -> string -> string option -> bool -> unit

(*s [save_module_to s f] saves the current environment as a module [s]
  in the file [f]. *)

val save_module_to : (Lib.library_segment -> Nametab.module_contents) -> 
  string -> string -> unit

(*s [module_segment m] returns the segment of the loaded module
    [m]; if not given, the segment of the current module is returned
    (which is then the same as [Lib.contents_after None]). 
    [module_filename] returns the full filename of a loaded module. *)

val module_segment : string option -> Lib.library_segment
val module_filename : string -> System.load_path_entry * string

(*s [fold_all_segments] and [iter_all_segments] iterate over all
    segments, the modules' segments first and then the current
    segment. Modules are presented in an arbitrary order. The given
    function is applied to all leaves (together with their section
    path). The boolean indicates if we must enter closed sections. *)

val fold_all_segments : bool -> ('a -> section_path -> obj -> 'a) -> 'a -> 'a
val iter_all_segments : bool -> (section_path -> obj -> unit) -> unit

(*s Global load path *)
val get_load_path : unit -> System.load_path
val add_load_path_entry : System.load_path_entry -> unit
val remove_path : string -> unit
