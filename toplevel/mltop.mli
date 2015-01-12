(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** {5 Toplevel management} *)

(** If there is a toplevel under Coq, it is described by the following
   record. *)
type toplevel = {
  load_obj : string -> unit;
  use_file : string -> unit;
  add_dir  : string -> unit;
  ml_loop  : unit -> unit }

(** Sets and initializes a toplevel (if any) *)
val set_top : toplevel -> unit

(** Are we in a native version of Coq? *)
val is_native : bool

(** Removes the toplevel (if any) *)
val remove : unit -> unit

(** Tests if an Ocaml toplevel runs under Coq *)
val is_ocaml_top : unit -> bool

(** Starts the Ocaml toplevel loop *)
val ocaml_toploop : unit -> unit

(** {5 ML Dynlink} *)

(** Tests if we can load ML files *)
val has_dynlink : bool

(** Dynamic loading of .cmo *)
val dir_ml_load : string -> unit

(** Dynamic interpretation of .ml *)
val dir_ml_use : string -> unit

(** Adds a path to the ML paths *)
val add_ml_dir : string -> unit
val add_rec_ml_dir : string -> unit

(** Adds a path to the Coq and ML paths *)
val add_path : unix_path:string -> coq_root:Names.DirPath.t -> implicit:bool -> unit
val add_rec_path : unix_path:string -> coq_root:Names.DirPath.t -> implicit:bool -> unit

(** List of modules linked to the toplevel *)
val add_known_module : string -> unit
val module_is_known : string -> bool
val load_ml_object : string -> string -> unit
val load_ml_object_raw : string -> unit
val load_ml_objects_raw_rex : Str.regexp -> unit

(** {5 Initialization functions} *)

(** Declare a plugin and its initialization function.
    A plugin is just an ML module with an initialization function.
    Adding a known plugin implies adding it as a known ML module.
    The initialization function is granted to be called after Coq is fully
    bootstrapped, even if the plugin is statically linked with the toplevel *)
val add_known_plugin : (unit -> unit) -> string -> unit

(** Calls all initialization functions in a non-specified order *)
val init_known_plugins : unit -> unit

(** Register a callback that will be called when the module is declared with
    the Declare ML Module command. This is useful to define Coq objects at that
    time only. Several functions can be defined for one module; they will be
    called in the order of declaration, and after the ML module has been
    properly initialized. *)
val declare_cache_obj : (unit -> unit) -> string -> unit

(** {5 Declaring modules} *)

val declare_ml_modules : Vernacexpr.locality_flag -> string list -> unit

(** {5 Utilities} *)

val print_ml_path : unit -> Pp.std_ppcmds
val print_ml_modules : unit -> Pp.std_ppcmds
val print_gc : unit -> Pp.std_ppcmds
