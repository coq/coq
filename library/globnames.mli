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
open Constr
open Mod_subst

val isVarRef : GlobRef.t -> bool
val isConstRef : GlobRef.t -> bool
val isIndRef : GlobRef.t -> bool
val isConstructRef : GlobRef.t -> bool

val canonical_gr : GlobRef.t -> GlobRef.t

val destVarRef : GlobRef.t -> variable
val destConstRef : GlobRef.t -> Constant.t
val destIndRef : GlobRef.t -> inductive
val destConstructRef : GlobRef.t -> constructor

val subst_global : substitution -> GlobRef.t -> GlobRef.t * constr Univ.univ_abstracted option
val subst_global_reference : substitution -> GlobRef.t -> GlobRef.t

(** Remove the last modpath segment *)
val pop_global_reference : GlobRef.t -> GlobRef.t

(** {6 Extended global references } *)

type abbreviation = KerName.t

type extended_global_reference =
  | TrueGlobal of GlobRef.t
  | Abbrev of abbreviation

val abbreviation_eq : abbreviation -> abbreviation -> bool

module ExtRefOrdered : sig
  type t = extended_global_reference
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end

module ExtRefSet : CSig.SetS with type elt = extended_global_reference
module ExtRefMap : CMap.ExtS
  with type key = extended_global_reference
   and module Set := ExtRefSet

val subst_extended_reference : substitution -> extended_global_reference -> extended_global_reference
