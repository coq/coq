(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Constr
open Mod_subst

(** {6 Global reference is a kernel side type for all references together } *)
type global_reference = GlobRef.t =
  | VarRef of variable           (** A reference to the section-context. *)
  | ConstRef of Constant.t       (** A reference to the environment. *)
  | IndRef of inductive          (** A reference to an inductive type. *)
  | ConstructRef of constructor  (** A reference to a constructor of an inductive type. *)
[@@ocaml.deprecated "Use Names.GlobRef.t"]

val isVarRef : GlobRef.t -> bool
val isConstRef : GlobRef.t -> bool
val isIndRef : GlobRef.t -> bool
val isConstructRef : GlobRef.t -> bool

val eq_gr : GlobRef.t -> GlobRef.t -> bool
[@@ocaml.deprecated "Use Names.GlobRef.equal"]
val canonical_gr : GlobRef.t -> GlobRef.t

val destVarRef : GlobRef.t -> variable
val destConstRef : GlobRef.t -> Constant.t
val destIndRef : GlobRef.t -> inductive
val destConstructRef : GlobRef.t -> constructor

val is_global : GlobRef.t -> constr -> bool

val subst_constructor : substitution -> constructor -> constructor * constr
val subst_global : substitution -> GlobRef.t -> GlobRef.t * constr
val subst_global_reference : substitution -> GlobRef.t -> GlobRef.t

(** This constr is not safe to be typechecked, universe polymorphism is not 
    handled here: just use for printing *)
val printable_constr_of_global : GlobRef.t -> constr

(** Turn a construction denoting a global reference into a global reference;
   raise [Not_found] if not a global reference *)
val global_of_constr : constr -> GlobRef.t

module RefOrdered : sig
  type t = GlobRef.t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end

module RefOrdered_env : sig
  type t = GlobRef.t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end

module Refset : CSig.SetS with type elt = GlobRef.t
module Refmap : Map.ExtS
  with type key = GlobRef.t and module Set := Refset

module Refset_env : CSig.SetS with type elt = GlobRef.t
module Refmap_env : Map.ExtS
  with type key = GlobRef.t and module Set := Refset_env

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

(** {6 Temporary function to brutally form kernel names from section paths } *)

val encode_mind : DirPath.t -> Id.t -> MutInd.t
val decode_mind : MutInd.t -> DirPath.t * Id.t
val encode_con : DirPath.t -> Id.t -> Constant.t
val decode_con : Constant.t -> DirPath.t * Id.t

(** {6 Popping one level of section in global names } *)
val pop_con : Constant.t -> Constant.t
val pop_kn : MutInd.t-> MutInd.t
val pop_global_reference : GlobRef.t -> GlobRef.t
