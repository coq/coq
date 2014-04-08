(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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

(** Tests if we can load ML files *)
val has_dynlink : bool

(** Starts the Ocaml toplevel loop *)
val ocaml_toploop : unit -> unit

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

(** Declare a plugin and its initialization function.
    A plugin is just an ML module with an initialization function.
    Adding a known plugin implies adding it as a known ML module.
    The initialization function is granted to be called after Coq is fully
    bootstrapped, even if the plugin is statically linked with the toplevel *)
val add_known_plugin : (unit -> unit) -> string -> unit

(** Calls all initialization functions in a non-specified order *)
val init_known_plugins : unit -> unit

val declare_ml_modules : Vernacexpr.locality_flag -> string list -> unit

val print_ml_path : unit -> Pp.std_ppcmds
val print_ml_modules : unit -> Pp.std_ppcmds
val print_gc : unit -> Pp.std_ppcmds
