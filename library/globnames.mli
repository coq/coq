(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

val subst_constructor : substitution -> constructor -> constructor
val subst_global : substitution -> GlobRef.t -> GlobRef.t * constr Univ.univ_abstracted option
val subst_global_reference : substitution -> GlobRef.t -> GlobRef.t

(** This constr is not safe to be typechecked, universe polymorphism is not
    handled here: just use for printing *)
val printable_constr_of_global : GlobRef.t -> constr

(** Turn a construction denoting a global reference into a global reference;
   raise [Not_found] if not a global reference *)
val global_of_constr : constr -> GlobRef.t

(** {6 Extended global references } *)

type syndef_name = KerName.t

type extended_global_reference =
  | TrueGlobal of GlobRef.t
  | SynDef of syndef_name

module ExtRefOrdered : sig
  type t = extended_global_reference
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end

type global_reference_or_constr =
  | IsGlobal of GlobRef.t
  | IsConstr of constr
