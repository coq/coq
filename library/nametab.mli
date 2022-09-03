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

(** This module contains the tables for globalization. *)

(** These globalization tables associate internal object references to
    qualified names (qualid). There are three classes of names:

    - 1a) internal kernel names: [kernel_name], [constant], [inductive],
         [module_path], [DirPath.t]

    - 1b) other internal names: [global_reference], [abbreviation],
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
   be stored by [library], where [obj_dir] is the "absolute" path and
   [obj_mp] is the current "module" prefix.

    Thus, for an object living inside [Module A. Section B.] the
   prefix would be:

    [ { obj_dir = "A.B"; obj_mp = "A"; } ]

    Note that [obj_dir] is a "path" that is to say,
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
    | DirOpenModule of ModPath.t
    | DirOpenModtype of ModPath.t
    | DirOpenSection of DirPath.t
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

(** Type of imperative nametabs *)
module type S = sig

  type elt
  type path

  val push : ?deprecated:Deprecation.t -> visibility -> path -> elt -> unit
  val remove : path -> elt -> unit
  val locate : qualid -> elt
  val locate_all : qualid -> elt list
  val exists : path -> bool
end

(** {6 Reverse lookup }
  Finding user names corresponding to the given
  internal name *)

(** Type of imperative nametabs with reverse resolution *)
module type SR = sig
  include S

  (** [path] Returns the full path bound to a [elt], and the (full)
     [path] associated to it *)
  val path : elt -> path

  (** The [shortest_qualid] functions given an object with [user_name]
      Coq.A.B.x, try to find the shortest among x, B.x, A.B.x and
      Coq.A.B.x that denotes the same object.
      @raise Not_found for unknown objects. *)
  val shortest_qualid : ?loc:Loc.t -> Names.Id.Set.t -> elt -> qualid
end

(***********************************************************************)
(** Nametab for [GlobRef.t]  *)

(** Helper *)
val locate_constant : qualid -> Constant.t

(** These functions globalize user-level references into global
   references, like [locate] and co, but raise a nice error message
   in case of failure *)
val global : qualid -> GlobRef.t
val global_inductive : qualid -> inductive

(** Mapping a full path to a global reference *)
val global_of_path : full_path -> GlobRef.t

(** Returns in particular the dirpath or the basename of the full path
   associated to global reference *)
val dirpath_of_global : GlobRef.t -> DirPath.t
val basename_of_global : GlobRef.t -> Id.t

(** Printing of global references using names as short as possible.
    @raise Not_found when the reference is not in the global tables. *)
val pr_global_env : Id.Set.t -> GlobRef.t -> Pp.t

module GlobRef : SR with type elt := GlobRef.t and type path := full_path

(***********************************************************************)
(** Abbreviations  *)
module Abbrev : SR with type elt := Globnames.abbreviation and type path := full_path

(***********************************************************************)
(** Common functions for Global Refs and abbreviations *)

(** These functions locate all global references with a given suffix;
   if [qualid] is valid as such, it comes first in the list *)
val locate_extended : qualid -> Globnames.extended_global_reference
val locate_extended_nowarn : qualid -> Globnames.extended_global_reference * Deprecation.t option
val locate_extended_all : qualid -> Globnames.extended_global_reference list
val extended_global_of_path : full_path -> Globnames.extended_global_reference

val warn_deprecated_xref : ?loc:Loc.t -> Deprecation.t -> Globnames.extended_global_reference -> unit

(** Locate qualids into full user names *)
val full_name_cci : qualid -> full_path

(** [completion_canditates qualid] will return the list of global
    references that have [qualid] as a prefix. UI usually will want to
    compose this with [shortest_qualid_of_global].
    Experimental API, note that it is _unstable_ *)
val completion_canditates : qualid -> Globnames.extended_global_reference list

(***********************************************************************)
(** Modules *)
module ModType : SR with type elt := ModPath.t and type path := full_path
val full_name_modtype : qualid -> full_path

module Module : SR with type elt := ModPath.t and type path := DirPath.t
val full_name_module : qualid -> DirPath.t

module Dir : S with type elt := GlobDirRef.t and type path := DirPath.t
val locate_section : qualid -> DirPath.t

(** Note for [Universe.path]: A universe_id might not be registered
   with a corresponding user name. @raise Not_found if the universe
   was not introduced by the user. *)
module Universe : SR with type elt := Univ.UGlobal.t and type path := full_path

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
  val remove : user_name -> t -> t
  val exists : user_name -> t -> bool
  val user_name : qualid -> t -> user_name
  val shortest_qualid_gen : ?loc:Loc.t -> (Id.t -> bool) -> user_name -> t -> qualid
  val shortest_qualid : ?loc:Loc.t -> Id.Set.t -> user_name -> t -> qualid
  val find_prefixes : qualid -> t -> elt list
  val match_prefixes : qualid -> t -> elt list
end

module Make (U : UserName) (E : EqualityType) :
  NAMETREE with type user_name = U.t and type elt = E.t

module Modules : sig
  type t
  val freeze : unit -> t
  val unfreeze : t -> unit
  val summary_tag : t Summary.Dyn.tag
end
