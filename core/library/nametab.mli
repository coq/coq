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
open Libnames
open Globnames

(** This module contains the tables for globalization. *)

(** These globalization tables associate internal object references to
    qualified names (qualid). There are three classes of names:

    - 1a) internal kernel names: [kernel_name], [constant], [inductive],
         [module_path], [DirPath.t]

    - 1b) other internal names: [global_reference], [syndef_name],
        [extended_global_reference], [global_dir_reference], ...

    - 2) full, non ambiguous user names: [full_path]

    - 3) non necessarily full, possibly ambiguous user names: [reference]
        and [qualid]
*)

(** Most functions in this module fall into one of the following categories:
{ul {- [push : visibility -> full_user_name -> object_reference -> unit]

     Registers the [object_reference] to be referred to by the
     [full_user_name] (and its suffixes according to [visibility]).
     [full_user_name] can either be a [full_path] or a [DirPath.t].
   }
   {- [exists : full_user_name -> bool]

     Is the [full_user_name] already attributed as an absolute user name
     of some object?
   }
   {- [locate : qualid -> object_reference]

     Finds the object referred to by [qualid] or raises [Not_found]
   }
   {- [full_name : qualid -> full_user_name]

     Finds the full user name referred to by [qualid] or raises [Not_found]
   }
   {- [shortest_qualid_of : object_reference -> user_name]

     The [user_name] can be for example the shortest non ambiguous [qualid] or
     the [full_user_name] or [Id.t]. Such a function can also have a
     local context argument.}}

*)

(** Object prefix morally contains the "prefix" naming of an object to
   be stored by [library], where [obj_dir] is the "absolute" path,
   [obj_mp] is the current "module" prefix and [obj_sec] is the
   "section" prefix.

    Thus, for an object living inside [Module A. Section B.] the
   prefix would be:

    [ { obj_dir = "A.B"; obj_mp = "A"; obj_sec = "B" } ]

    Note that both [obj_dir] and [obj_sec] are "paths" that is to say,
   as opposed to [obj_mp] which is a single module name.

 *)
type object_prefix = {
  obj_dir : DirPath.t;
  obj_mp  : ModPath.t;
}

val eq_op : object_prefix -> object_prefix -> bool

(** to this type are mapped [DirPath.t]'s in the nametab *)
module GlobDirRef : sig
  type t =
    | DirOpenModule of object_prefix
    | DirOpenModtype of object_prefix
    | DirOpenSection of object_prefix
    | DirModule of object_prefix
  val equal : t -> t -> bool
end

exception GlobalizationError of qualid

(** Raises a globalization error *)
val error_global_not_found : info:Exninfo.info -> qualid -> 'a

(** {6 Register visibility of things } *)

(** The visibility can be registered either
   - for all suffixes not shorter then a given int -- when the
   object is loaded inside a module -- or
   - for a precise suffix, when the module containing (the module
   containing ...) the object is opened (imported)

*)

type visibility = Until of int | Exactly of int

val map_visibility : (int -> int) -> visibility -> visibility

val push : visibility -> full_path -> GlobRef.t -> unit
val push_modtype : visibility -> full_path -> ModPath.t -> unit
val push_dir : visibility -> DirPath.t -> GlobDirRef.t -> unit
val push_syndef : visibility -> full_path -> syndef_name -> unit

module UnivIdMap : CMap.ExtS with type key = Univ.Level.UGlobal.t

val push_universe : visibility -> full_path -> Univ.Level.UGlobal.t -> unit

(** {6 The following functions perform globalization of qualified names } *)

(** These functions globalize a (partially) qualified name or fail with
   [Not_found] *)

val locate : qualid -> GlobRef.t
val locate_extended : qualid -> extended_global_reference
val locate_constant : qualid -> Constant.t
val locate_syndef : qualid -> syndef_name
val locate_modtype : qualid -> ModPath.t
val locate_dir : qualid -> GlobDirRef.t
val locate_module : qualid -> ModPath.t
val locate_section : qualid -> DirPath.t
val locate_universe : qualid -> Univ.Level.UGlobal.t

(** These functions globalize user-level references into global
   references, like [locate] and co, but raise a nice error message
   in case of failure *)

val global : qualid -> GlobRef.t
val global_inductive : qualid -> inductive

(** These functions locate all global references with a given suffix;
   if [qualid] is valid as such, it comes first in the list *)

val locate_all : qualid -> GlobRef.t list
val locate_extended_all : qualid -> extended_global_reference list
val locate_extended_all_dir : qualid -> GlobDirRef.t list
val locate_extended_all_modtype : qualid -> ModPath.t list

(** Experimental completion support, API is _unstable_ *)
val completion_canditates : qualid -> extended_global_reference list
(** [completion_canditates qualid] will return the list of global
    references that have [qualid] as a prefix. UI usually will want to
    compose this with [shortest_qualid_of_global] *)

(** Mapping a full path to a global reference *)

val global_of_path : full_path -> GlobRef.t
val extended_global_of_path : full_path -> extended_global_reference

(** {6 These functions tell if the given absolute name is already taken } *)

val exists_cci : full_path -> bool
val exists_modtype : full_path -> bool
val exists_dir : DirPath.t -> bool
val exists_universe : full_path -> bool

(** {6 These functions locate qualids into full user names } *)

val full_name_cci : qualid -> full_path
val full_name_modtype : qualid -> full_path
val full_name_module : qualid -> DirPath.t

(** {6 Reverse lookup }
  Finding user names corresponding to the given
  internal name *)

(** Returns the full path bound to a global reference or syntactic
   definition, and the (full) dirpath associated to a module path *)

val path_of_syndef : syndef_name -> full_path
val path_of_global : GlobRef.t -> full_path
val dirpath_of_module : ModPath.t -> DirPath.t
val path_of_modtype : ModPath.t -> full_path

(** A universe_id might not be registered with a corresponding user name.
    @raise Not_found if the universe was not introduced by the user. *)
val path_of_universe : Univ.Level.UGlobal.t -> full_path

(** Returns in particular the dirpath or the basename of the full path
   associated to global reference *)

val dirpath_of_global : GlobRef.t -> DirPath.t
val basename_of_global : GlobRef.t -> Id.t

(** Printing of global references using names as short as possible.
    @raise Not_found when the reference is not in the global tables. *)
val pr_global_env : Id.Set.t -> GlobRef.t -> Pp.t


(** The [shortest_qualid] functions given an object with [user_name]
   Coq.A.B.x, try to find the shortest among x, B.x, A.B.x and
   Coq.A.B.x that denotes the same object.
   @raise Not_found for unknown objects. *)

val shortest_qualid_of_global : ?loc:Loc.t -> Id.Set.t -> GlobRef.t -> qualid
val shortest_qualid_of_syndef : ?loc:Loc.t -> Id.Set.t -> syndef_name -> qualid
val shortest_qualid_of_modtype : ?loc:Loc.t -> ModPath.t -> qualid
val shortest_qualid_of_module : ?loc:Loc.t -> ModPath.t -> qualid

(** In general we have a [UnivNames.universe_binders] around rather than a [Id.Set.t] *)
val shortest_qualid_of_universe : ?loc:Loc.t -> 'u Id.Map.t -> Univ.Level.UGlobal.t -> qualid

(** {5 Generic name handling} *)

(** NOT FOR PUBLIC USE YET. Plugin writers, please do not rely on this API. *)

module type UserName = sig
  type t
  val equal : t -> t -> bool
  val to_string : t -> string
  val repr : t -> Id.t * module_ident list
end

module type EqualityType =
sig
  type t
  val equal : t -> t -> bool
end

module type NAMETREE = sig
  type elt
  type t
  type user_name

  val empty : t
  val push : visibility -> user_name -> elt -> t -> t
  val locate : qualid -> t -> elt
  val find : user_name -> t -> elt
  val exists : user_name -> t -> bool
  val user_name : qualid -> t -> user_name
  val shortest_qualid_gen : ?loc:Loc.t -> (Id.t -> bool) -> user_name -> t -> qualid
  val shortest_qualid : ?loc:Loc.t -> Id.Set.t -> user_name -> t -> qualid
  val find_prefixes : qualid -> t -> elt list
  val match_prefixes : qualid -> t -> elt list
end

module Make (U : UserName) (E : EqualityType) :
  NAMETREE with type user_name = U.t and type elt = E.t
