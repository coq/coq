(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

type module_kind = Module | ModType | ModAny

type 'modast module_interpretor =
  Environ.env -> module_kind -> 'modast ->
    Entries.module_struct_entry * module_kind * Univ.ContextSet.t

type 'modast module_params =
  (lident list * ('modast * inline)) list

(** [declare_module interp_modast id fargs typ exprs]
   declares module [id], with structure constructed by [interp_modast]
   from functor arguments [fargs], with final type [typ].
   [exprs] is usually of length 1 (Module definition with a concrete
   body), but it could also be empty ("Declare Module", with non-empty [typ]),
   or multiple (body of the shape M <+ N <+ ...). *)

val declare_module :
  'modast module_interpretor ->
  Id.t ->
  'modast module_params ->
  ('modast * inline) module_signature ->
  ('modast * inline) list -> ModPath.t

val start_module :
  'modast module_interpretor ->
  bool option -> Id.t ->
  'modast module_params ->
  ('modast * inline) module_signature -> ModPath.t

val end_module : unit -> ModPath.t



(** {6 Module types } *)

(** [declare_modtype interp_modast id fargs typs exprs]
    Similar to [declare_module], except that the types could be multiple *)

val declare_modtype :
  'modast module_interpretor ->
  Id.t ->
  'modast module_params ->
  ('modast * inline) list ->
  ('modast * inline) list ->
  ModPath.t

val start_modtype :
  'modast module_interpretor ->
  Id.t ->
  'modast module_params ->
  ('modast * inline) list -> ModPath.t

val end_modtype : unit -> ModPath.t

(** {6 Libraries i.e. modules on disk } *)

type library_name = DirPath.t

type library_objects

val register_library :
  library_name ->
  Safe_typing.compiled_library -> library_objects -> Safe_typing.vodigest ->
  Univ.ContextSet.t -> unit

val get_library_native_symbols : library_name -> Nativecode.symbols

val start_library : library_name -> unit

val end_library :
  ?except:Future.UUIDSet.t -> library_name ->
    Safe_typing.compiled_library * library_objects * Safe_typing.native_library

(** append a function to be executed at end_library *)
val append_end_library_hook : (unit -> unit) -> unit

(** [really_import_module mp] opens the module [mp] (in a Caml sense).
   It modifies Nametab and performs the [open_object] function for
   every object of the module. Raises [Not_found] when [mp] is unknown
   or when [mp] corresponds to a functor. *)

val really_import_module : ModPath.t -> unit

(** [import_module export mp] is a synchronous version of
   [really_import_module]. If [export] is [true], the module is also
   opened every time the module containing it is. *)

val import_module : bool -> ModPath.t -> unit

(** Include  *)

val declare_include :
  'modast module_interpretor -> ('modast * inline) list -> unit

(** {6 ... } *)
(** [iter_all_segments] iterate over all segments, the modules'
    segments first and then the current segment. Modules are presented
    in an arbitrary order. The given function is applied to all leaves
    (together with their section path). *)

val iter_all_segments :
  (Libnames.object_name -> Libobject.obj -> unit) -> unit


val debug_print_modtab : unit -> Pp.t

(** For printing modules, [process_module_binding] adds names of
    bound module (and its components) to Nametab. It also loads
    objects associated to it. It may raise a [Failure] when the
    bound module hasn't an atomic type. *)

val process_module_binding :
  MBId.t -> Declarations.module_alg_expr -> unit
