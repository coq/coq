(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** {6 Modules } *)

(** Rigid / flexible module signature *)

type 'a module_signature =
  | Enforce of 'a (** ... : T *)
  | Check of 'a list (** ... <: T1 <: T2, possibly empty *)

(** Which module inline annotations should we honor,
    either None or the ones whose level is less or equal
    to the given integer *)

type inline =
  | NoInline
  | DefaultInline
  | InlineAt of int

(** Kinds of modules *)

type module_params = (lident list * (Constrexpr.module_ast * inline)) list

(** [declare_module id fargs typ exprs] declares module [id], from
   functor arguments [fargs], with final type [typ].  [exprs] is
   usually of length 1 (Module definition with a concrete body), but
   it could also be empty ("Declare Module", with non-empty [typ]), or
   multiple (body of the shape M <+ N <+ ...). *)

val declare_module :
  Id.t ->
  module_params ->
  (Constrexpr.module_ast * inline) module_signature ->
  (Constrexpr.module_ast * inline) list -> ModPath.t

val start_module :
  bool option -> Id.t ->
  module_params ->
  (Constrexpr.module_ast * inline) module_signature -> ModPath.t

val end_module : unit -> ModPath.t



(** {6 Module types } *)

(** [declare_modtype interp_modast id fargs typs exprs]
    Similar to [declare_module], except that the types could be multiple *)

val declare_modtype :
  Id.t ->
  module_params ->
  (Constrexpr.module_ast * inline) list ->
  (Constrexpr.module_ast * inline) list ->
  ModPath.t

val start_modtype :
  Id.t ->
  module_params ->
  (Constrexpr.module_ast * inline) list -> ModPath.t

val end_modtype : unit -> ModPath.t

(** {6 Libraries i.e. modules on disk } *)

type library_name = DirPath.t

type library_objects

val register_library :
  library_name ->
  Safe_typing.compiled_library -> library_objects -> Safe_typing.vodigest ->
  Univ.ContextSet.t -> unit

val start_library : library_name -> unit

val end_library :
  output_native_objects:bool -> library_name ->
    Safe_typing.compiled_library * library_objects * Nativelib.native_library

(** append a function to be executed at end_library *)
val append_end_library_hook : (unit -> unit) -> unit

(** [import_module export mp] imports the module [mp].
   It modifies Nametab and performs the [open_object] function for
   every object of the module. Raises [Not_found] when [mp] is unknown
   or when [mp] corresponds to a functor. If [export] is [true], the module is also
   opened every time the module containing it is. *)

val import_module : Libobject.open_filter -> export:bool -> ModPath.t -> unit

(** Same as [import_module] but for multiple modules, and more optimized than
    iterating [import_module]. *)
val import_modules : export:bool -> (Libobject.open_filter * ModPath.t) list -> unit

(** Include  *)

val declare_include : (Constrexpr.module_ast * inline) list -> unit

(** {6 ... } *)
(** [iter_all_segments] iterate over all segments, the modules'
    segments first and then the current segment. Modules are presented
    in an arbitrary order. The given function is applied to all leaves
    (together with their section path). *)

val iter_all_segments :
  (Libobject.object_name -> Libobject.t -> unit) -> unit


val debug_print_modtab : unit -> Pp.t

(** For printing modules, [process_module_binding] adds names of
    bound module (and its components) to Nametab. It also loads
    objects associated to it. It may raise a [Failure] when the
    bound module hasn't an atomic type. *)

val process_module_binding :
  MBId.t -> Declarations.module_alg_expr -> unit
