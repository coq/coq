(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Vernacexpr

(** {6 Modules } *)

type 'modast module_interpretor =
  Environ.env -> Misctypes.module_kind -> 'modast ->
    Entries.module_struct_entry * Misctypes.module_kind

type 'modast module_params =
  (Id.t Loc.located list * ('modast * inline)) list

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
  ('modast * inline) list -> module_path

val start_module :
  'modast module_interpretor ->
  bool option -> Id.t ->
  'modast module_params ->
  ('modast * inline) module_signature -> module_path

val end_module : unit -> module_path



(** {6 Module types } *)

(** [declare_modtype interp_modast id fargs typs exprs]
    Similar to [declare_module], except that the types could be multiple *)

val declare_modtype :
  'modast module_interpretor ->
  Id.t ->
  'modast module_params ->
  ('modast * inline) list ->
  ('modast * inline) list ->
  module_path

val start_modtype :
  'modast module_interpretor ->
  Id.t ->
  'modast module_params ->
  ('modast * inline) list -> module_path

val end_modtype : unit -> module_path


(** {6 Libraries i.e. modules on disk } *)

type library_name = DirPath.t

type library_objects

val register_library :
  library_name ->
  Safe_typing.compiled_library -> library_objects -> Safe_typing.vodigest ->
  Univ.universe_context_set -> unit

val get_library_symbols_tbl : library_name -> Nativecode.symbol array

val start_library : library_name -> unit

val end_library :
  ?except:Future.UUIDSet.t -> library_name ->
    Safe_typing.compiled_library * library_objects * Safe_typing.native_library

(** [really_import_module mp] opens the module [mp] (in a Caml sense).
   It modifies Nametab and performs the [open_object] function for
   every object of the module. Raises [Not_found] when [mp] is unknown
   or when [mp] corresponds to a functor. *)

val really_import_module : module_path -> unit

(** [import_module export mp] is a synchronous version of
   [really_import_module]. If [export] is [true], the module is also
   opened every time the module containing it is. *)

val import_module : bool -> module_path -> unit

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


val debug_print_modtab : unit -> Pp.std_ppcmds

(** For printing modules, [process_module_binding] adds names of
    bound module (and its components) to Nametab. It also loads
    objects associated to it. It may raise a [Failure] when the
    bound module hasn't an atomic type. *)

val process_module_binding :
  MBId.t -> Declarations.module_alg_expr -> unit
