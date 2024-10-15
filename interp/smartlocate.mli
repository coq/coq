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
open Libnames
open Globnames

(** [locate_global_with_alias] locates global reference possibly following
   a notation if this notation has a role of aliasing; raise [Not_found]
   if not bound in the global env; raise a [UserError] if bound to a
   syntactic def that does not denote a reference *)

val locate_global_with_alias : ?head:bool -> qualid -> GlobRef.t

(** Extract a global_reference from a reference that can be an "alias".
    If the reference points to a more complex term, we return None *)
val global_of_extended_global : extended_global_reference -> GlobRef.t option

(** Locate a reference taking into account possible "alias" notations.
    May raise [Nametab.GlobalizationError _] for an unknown reference,
    or a [UserError] if bound to a syntactic def that does not denote
    a reference. *)
val global_with_alias : ?head:bool -> qualid -> GlobRef.t

(** The same for constants *)
val global_constant_with_alias : qualid -> Constant.t

(** The same for inductive types *)
val global_inductive_with_alias : qualid -> inductive

(** The same for constructors of an inductive type *)
val global_constructor_with_alias : qualid -> constructor

(** Locate a reference taking into account notations and "aliases" *)
val smart_global : ?head:bool -> qualid Constrexpr.or_by_notation -> GlobRef.t

(** The same for constants *)
val smart_global_constant : qualid Constrexpr.or_by_notation -> Constant.t

(** The same for inductive types *)
val smart_global_inductive : qualid Constrexpr.or_by_notation -> inductive

(** The same for constructors of an inductive type *)
val smart_global_constructor : qualid Constrexpr.or_by_notation -> constructor
