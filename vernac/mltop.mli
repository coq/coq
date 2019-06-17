(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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

(** Removes the toplevel (if any) *)
val remove : unit -> unit

(** Tests if an Ocaml toplevel runs under Coq *)
val is_ocaml_top : unit -> bool

(** Starts the Ocaml toplevel loop *)
val ocaml_toploop : unit -> unit

(** {5 ML Dynlink} *)

(** Adds a dir to the plugin search path *)
val add_ml_dir : recursive:bool -> string -> unit

(** Tests if we can load ML files *)
val has_dynlink : bool

(** Dynamic loading of .cmo *)
val dir_ml_load : string -> unit

(** Dynamic interpretation of .ml *)
val dir_ml_use : string -> unit

(** List of modules linked to the toplevel *)
val add_known_module : string -> unit
val module_is_known : string -> bool

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

val print_ml_path : unit -> Pp.t
val print_ml_modules : unit -> Pp.t
val print_gc : unit -> Pp.t
