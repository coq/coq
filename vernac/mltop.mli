(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {5 Toplevel management} *)

(** Coq plugins are identified by their OCaml library name (in the
   Findlib sense) *)
module PluginSpec : sig

  (** A plugin is identified by its canonical library name,
      such as [coq-core.plugins.ltac] *)
  type t

  (** [repr p] returns a pair of [legacy_name, lib_name] where
     [lib_name] is the canoncial library name.

      [legacy_name] may be [Some pname] for the cases the plugin was
     specified in [Declare ML Module] with their legacy name (for
     example [ltac_plugin]). This will stop being supported soon and
     is only here for compatiblity. Note that the name doesn't include
     the ".cmxs" / ".cma" extension *)
  val repr : t -> string option * string

  val pp : t -> string
end

type toplevel =
  { load_plugin : PluginSpec.t -> unit
  (** Load a findlib library, given by public name *)
  ; load_module : string -> unit
  (** Load a cmxs / cmo module, used by the native compiler to load objects *)
  ; add_dir  : string -> unit
  (** Adds a dir to the module search path *)
  ; ml_loop  : unit -> unit
  (** Implementation of Drop *)
  }

(** Sets and initializes a toplevel (if any) *)
val set_top : toplevel -> unit

(** Removes the toplevel (if any) *)
val remove : unit -> unit

(** Tests if an Ocaml toplevel runs under Coq *)
val is_ocaml_top : unit -> bool

(** Starts the Ocaml toplevel loop *)
val ocaml_toploop : unit -> unit

(** {5 ML Dynlink} *)

(** Adds a dir to the plugin search path, this also extends
   OCamlfind's search path *)
val add_ml_dir : string -> unit

(** Tests if we can load ML files *)
val has_dynlink : bool

val module_is_known : string -> bool

(** {5 Initialization functions} *)

(** Declare a plugin without an initialization function.  A plugin is
   a findlib library name. Usually, this will be called automatically
   when use do [DECLARE PLUGIN "pkg.lib"] in the .mlg file. *)
val add_known_module : string -> unit
(* EJGA: Todo, this could take a PluginSpec.t at some point *)

(** Declare a plugin plus a Coq-specific initialization function.
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

(** Implementation of the [Declare ML Module] vernacular command. *)
val declare_ml_modules : Vernacexpr.locality_flag -> string list -> unit

(** {5 Utilities} *)

val print_ml_path : unit -> Pp.t
val print_ml_modules : unit -> Pp.t
val print_gc : unit -> Pp.t
