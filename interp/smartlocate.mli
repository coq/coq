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
open Libnames
open Globnames

(** [locate_global_with_alias] locates global reference possibly following
   a notation if this notation has a role of aliasing; raise [Not_found]
   if not bound in the global env; raise a [UserError] if bound to a
   syntactic def that does not denote a reference *)

val locate_global_with_alias : ?head:bool -> qualid -> GlobRef.t

(** Extract a global_reference from a reference that can be an "alias" *)
val global_of_extended_global : extended_global_reference -> GlobRef.t

(** Locate a reference taking into account possible "alias" notations.
    May raise [Nametab.GlobalizationError _] for an unknown reference,
    or a [UserError] if bound to a syntactic def that does not denote
    a reference. *)
val global_with_alias : ?head:bool -> qualid -> GlobRef.t

(** The same for inductive types *)
val global_inductive_with_alias : qualid -> inductive

(** Locate a reference taking into account notations and "aliases" *)
val smart_global : ?head:bool -> qualid Constrexpr.or_by_notation -> GlobRef.t

(** The same for inductive types *)
val smart_global_inductive : qualid Constrexpr.or_by_notation -> inductive
