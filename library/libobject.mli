(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Nametab
open Mod_subst

(** [Libobject] declares persistent objects, given with methods:

   * a caching function specifying how to add the object in the current
     scope; called when the object is added and after the end of the containing
     sections.
     If the object wishes to register its visibility in the Nametab,
     it should do so for all possible suffixes.

   * a loading function, specifying what to do when the module
     containing the object is loaded; called at Require
     and after the end of the containing modules.
     If the object wishes to register its visibility in the Nametab,
     it should do so for all suffixes no shorter than the "int" argument

   * an opening function, specifying what to do when the module
     containing the object is opened; called when the containing modules
     are Imported.
     Objects which should only have an effect when the nearest containing module
     is imported (and not when the modules containing the nearest module are imported)
     must check that the "int" argument is [1].
     If the object wishes to register its visibility in the Nametab,
     it should do so for the suffix of the length the "int" argument

   * a classification function, specifying what to do with the object,
     when the current module (containing the object) is ended;
     The possibilities are:
     Dispose    - the object is dropped at the end of the module.
     Substitute - the object is kept at the end of the module.
       When the module is cloned (Include, module aliases)
       or when it's a module type which is getting instantiated
       (eg if module type [T] is used for a functor argument [X : T]
        or [Declare Module X : T]),
       the substitution function is called on the object to update the module name.
     Keep       - the object is kept at the end of the module.
       When the module is cloned the object is not cloned with it.
       This means that Keep objects in a module type or functor are dropped.
     Escape     - like Keep, but also escapes module types, functors and opaque modules.
       Monomorphic universes and universe constraints behave like this.
     Anticipate - this is for objects that have to be explicitly managed
       by the [end_module] function (currently only Require).

   * a substitution function, performing the substitution;
     this function should be declared for substitutive objects
     only (see above). NB: the substitution might be delayed
     instead of happening at module creation, so this function
     should _not_ depend on the current environment

   * a discharge function, that is called at section closing time to
     collect the data necessary to rebuild the discharged form of the
     non volatile objects. If it returns [None] the object is dropped.
     It is called in the state inside the section at its end, before it is reset.
     Notably the global environment contains the section data and the non-discharged globals.

   * a rebuild function, that is applied after section closing to
     rebuild the non volatile content of a section from the data
     collected by the discharge function
     It is called in the state after the end of the section with any previous objects already present.
     Notably the global environment contains the discharged globals.

  Any type defined as a persistent object must be pure (e.g. no references) and
  marshallable by the OCaml Marshal module (e.g. no closures).

*)

type substitutivity = Dispose | Substitute | Keep | Escape | Anticipate

(** Both names are passed to objects: a "semantic" [kernel_name], which
   can be substituted and a "syntactic" [full_path] which can be printed
*)

type object_name = Libnames.full_path * KerName.t

type open_filter

type ('a,'b,'discharged) object_declaration = {
  object_name : string;
  object_stage : Summary.Stage.t;
  cache_function : 'b -> unit;
  load_function : int -> 'b -> unit;
  open_function : open_filter -> int -> 'b -> unit;
  classify_function : 'a -> substitutivity;
  subst_function :  substitution * 'a -> 'a;
  discharge_function : 'a -> 'discharged option;
  rebuild_function : 'discharged -> 'a;
}

val unfiltered : open_filter

val make_filter : finite:bool -> string CAst.t list -> open_filter
(** Anomaly when the list is empty. *)

type category

val create_category : string -> category
(** Anomaly if called more than once for a given string. *)

val in_filter : cat:category option -> open_filter -> bool
(** On [cat:None], returns whether the filter allows opening
   uncategorized objects.

    On [cat:(Some category)], returns whether the filter allows
   opening objects in the given [category]. *)

val simple_open : ?cat:category -> ('i -> 'a -> unit) ->
  open_filter -> 'i -> 'a -> unit
(** Combinator for making objects with simple category-based open
   behaviour. When [cat:None], can be opened by Unfiltered, but also
   by Filtered with a negative set. *)

val filter_eq : open_filter -> open_filter -> bool

val filter_and : open_filter -> open_filter -> open_filter option
(** Returns [None] when the intersection is empty. *)

val filter_or :  open_filter -> open_filter -> open_filter

(** The default object has empty methods.
   Object creators are advised to use the construction
   [{(default_object "MY_OBJECT") with
      cache_function = ...
   }]
   and specify only these functions which are not empty/meaningless

    The classify_function must be specified.
*)

val default_object : ?stage:Summary.Stage.t -> string -> ('a,'b,'a) object_declaration

(** the identity substitution function *)
val ident_subst_function : substitution * 'a -> 'a

(** {6 ... } *)
(** Given an object declaration, the function [declare_object_full]
   will hand back two functions, the "injection" and "projection"
   functions for dynamically typed library-objects. *)

module Dyn : Dyn.S

type obj = Dyn.t

module ExportObj : sig
  type t = { mpl : (open_filter * Names.ModPath.t) list } [@@unboxed]
end

type algebraic_objects =
  | Objs of t list
  | Ref of ModPath.t * Mod_subst.substitution

(* there are some extra invariants we could try to enforce by typing:
   - substitutive_objects do not contain KeepObject and EscapeObject
   - KeepObject only contains itself and atoms
   - EscapeObject only contains itself and atoms *)
and t =
  | ModuleObject of Id.t * substitutive_objects
  | ModuleTypeObject of Id.t * substitutive_objects
  | IncludeObject of algebraic_objects
  | KeepObject of Id.t * t list
  | EscapeObject of Id.t * t list
  | ExportObject of ExportObj.t
  | AtomicObject of obj

and substitutive_objects = MBId.t list * algebraic_objects

(** Object declaration and names: if you need the current prefix
   (typically to interact with the nametab), you need to have it
   passed to you.

    - [declare_named_object_gen] passes the raw prefix which you can
    manipulate as you wish.

    - [declare_named_object_full] and [declare_named_object] provide
   the convenience of packaging it with the provided [Id.t] into a
   [object_name].

    - [declare_object] and [declare_object_full] ignore the prefix for you. *)

val declare_object :
  ('a, 'a, _) object_declaration -> ('a -> obj)

val declare_object_full :
  ('a, 'a, _) object_declaration -> 'a Dyn.tag

val declare_named_object_full :
  ('a, object_name * 'a, _) object_declaration -> (Id.t * 'a) Dyn.tag

val declare_named_object :
  ('a, object_name * 'a, _) object_declaration -> (Id.t -> 'a -> obj)

val declare_named_object_gen :
  ('a, object_prefix * 'a, _) object_declaration -> ('a -> obj)

val cache_object : object_prefix * obj -> unit
val load_object : int -> object_prefix * obj -> unit
val open_object : open_filter -> int -> object_prefix * obj -> unit
val subst_object : substitution * obj -> obj
val classify_object : obj -> substitutivity
val object_stage : obj -> Summary.Stage.t

type discharged_obj

val discharge_object : obj -> discharged_obj option
val rebuild_object : discharged_obj -> obj

type locality = Local | Export | SuperGlobal

(** Object with semi-static scoping: the scoping depends on the given
    [locality] not the rest of the object.

    It is up to the caller of [add_leaf] to produce sensible errors if
    a value which cannot be discharged is given with non Local
    locality.

    If [subst] is [None] non [Local] values are [Keep], otherwise [Substitute].

    [Export] values are only imported with shallow imports (depth = 1).

    [cat] only matters when importing, ie only for [Export] values.
*)
val object_with_locality : ?stage:Summary.Stage.t -> ?cat:category -> string ->
  cache:('a -> unit) ->
  subst:(Mod_subst.substitution * 'a -> 'a) option ->
  discharge:('a -> 'a) ->
  (locality * 'a, locality * 'a, locality * 'a) object_declaration

(** Higher-level API for objects with fixed scope.

- Local means that the object cannot be imported from outside.
- Global means that it can be imported (by importing the module that contains the
object).
- Superglobal means that the object survives to closing a module, and is imported
when the file which contains it is Required (even without Import).
- With the nodischarge variants, the object does not survive section closing.
  With the normal variants, it does.

We recommend to avoid declaring superglobal objects and using the nodischarge
variants.
*)

val local_object : ?stage:Summary.Stage.t -> string ->
  cache:('a -> unit) ->
  discharge:('a -> 'a option) ->
  ('a,'a,'a) object_declaration

val local_object_nodischarge : ?stage:Summary.Stage.t -> string ->
  cache:('a -> unit) ->
  ('a,'a,'a) object_declaration

val global_object : ?cat:category -> ?stage:Summary.Stage.t -> string ->
  cache:('a -> unit) ->
  subst:(Mod_subst.substitution * 'a -> 'a) option ->
  discharge:('a -> 'a option) ->
  ('a,'a,'a) object_declaration

val global_object_nodischarge : ?cat:category -> ?stage:Summary.Stage.t -> string ->
  cache:('a -> unit) ->
  subst:(Mod_subst.substitution * 'a -> 'a) option ->
  ('a,'a,'a) object_declaration

val superglobal_object : ?stage:Summary.Stage.t -> string ->
  cache:('a -> unit) ->
  subst:(Mod_subst.substitution * 'a -> 'a) option ->
  discharge:('a -> 'a option) ->
  ('a,'a,'a) object_declaration

val superglobal_object_nodischarge : ?stage:Summary.Stage.t -> string ->
  cache:('a -> unit) ->
  subst:(Mod_subst.substitution * 'a -> 'a) option ->
  ('a,'a,'a) object_declaration

(** {6 Debug} *)

val dump : unit -> (int * string) list
