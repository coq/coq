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

type global_reference = GlobRef.t =
  | VarRef of variable     [@ocaml.deprecated "Use Names.GlobRef.VarRef"]
  | ConstRef of Constant.t [@ocaml.deprecated "Use Names.GlobRef.ConstRef"]
  | IndRef of inductive    [@ocaml.deprecated "Use Names.GlobRef.IndRef"]
  | ConstructRef of constructor [@ocaml.deprecated "Use Names.GlobRef.ConstructRef"]
[@@ocaml.deprecated "Use Names.GlobRef.t"]

val isVarRef : GlobRef.t -> bool
val isConstRef : GlobRef.t -> bool
val isIndRef : GlobRef.t -> bool
val isConstructRef : GlobRef.t -> bool

val canonical_gr : GlobRef.t -> GlobRef.t

val destVarRef : GlobRef.t -> variable
val destConstRef : GlobRef.t -> Constant.t
val destIndRef : GlobRef.t -> inductive
val destConstructRef : GlobRef.t -> constructor

val is_global : GlobRef.t -> constr -> bool
[@@ocaml.deprecated "Use [Constr.isRefX] instead."]

val subst_global : substitution -> GlobRef.t -> GlobRef.t * constr Univ.univ_abstracted option
val subst_global_reference : substitution -> GlobRef.t -> GlobRef.t

(** This constr is not safe to be typechecked, universe polymorphism is not
    handled here: just use for printing *)
val printable_constr_of_global : GlobRef.t -> constr

(** Turn a construction denoting a global reference into a global reference;
   raise [Not_found] if not a global reference *)
val global_of_constr : constr -> GlobRef.t
[@@ocaml.deprecated "Use [Constr.destRef] instead (throws DestKO instead of Not_found)."]

(** {6 Extended global references } *)

type abbreviation = KerName.t

type extended_global_reference =
  | TrueGlobal of GlobRef.t
  | Abbrev of abbreviation

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
