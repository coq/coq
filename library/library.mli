
(* $Id$ *)

(* This module is the heart of the library. It provides low level functions to
   load, open and save modules. Modules are saved onto the disk with checksums
   (obtained with the [Digest] module), which are checked at loading time to
   prevent inconsistencies between files written at various dates. It also
   provides a high level function [require] which corresponds to the 
   vernacular command [Require]. *)

val load_module : string -> string option -> unit
val open_module : string -> unit

val module_is_loaded : string -> bool
val module_is_opened : string -> bool

(*s Require. The command [require_module spec m file export] loads and opens
  a module [m]. [file] specifies the filename, if not [None]. [spec]
  specifies to look for a specification ([true]) or for an implementation
  ([false]), if not [None]. And [export] specifies if the module must be 
  exported. *)

val require_module : bool option -> string -> string option -> bool -> unit

(*s [save_module_to s f] saves the current environment as a module [s]
  in the file [f]. *)

val save_module_to : string -> string -> unit

