(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Constr
open Mod_subst

val isVarRef : global_reference -> bool
val isConstRef : global_reference -> bool
val isIndRef : global_reference -> bool
val isConstructRef : global_reference -> bool

val eq_gr : global_reference -> global_reference -> bool
val canonical_gr : global_reference -> global_reference

val destVarRef : global_reference -> variable
val destConstRef : global_reference -> Constant.t
val destIndRef : global_reference -> inductive
val destConstructRef : global_reference -> constructor

val is_global : global_reference -> constr -> bool

val subst_constructor : substitution -> constructor -> constructor * constr
val subst_global : substitution -> global_reference -> global_reference * constr
val subst_global_reference : substitution -> global_reference -> global_reference

(** This constr is not safe to be typechecked, universe polymorphism is not 
    handled here: just use for printing *)
val printable_constr_of_global : global_reference -> constr

(** Turn a construction denoting a global reference into a global reference;
   raise [Not_found] if not a global reference *)
val global_of_constr : constr -> global_reference

(** Obsolete synonyms for constr_of_global and global_of_constr *)
val reference_of_constr : constr -> global_reference
[@@ocaml.deprecated "Alias of Globnames.global_of_constr"]

module RefOrdered : sig
  type t = global_reference
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end

module RefOrdered_env : sig
  type t = global_reference
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end

module Refset : CSig.SetS with type elt = global_reference
module Refmap : Map.ExtS
  with type key = global_reference and module Set := Refset

module Refset_env : CSig.SetS with type elt = global_reference
module Refmap_env : Map.ExtS
  with type key = global_reference and module Set := Refset_env

(** {6 Extended global references } *)

type syndef_name = KerName.t

type extended_global_reference =
  | TrueGlobal of global_reference
  | SynDef of syndef_name

module ExtRefOrdered : sig
  type t = extended_global_reference
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end

type global_reference_or_constr = 
  | IsGlobal of global_reference
  | IsConstr of constr

(** {6 Temporary function to brutally form kernel names from section paths } *)

val encode_mind : DirPath.t -> Id.t -> MutInd.t
val decode_mind : MutInd.t -> DirPath.t * Id.t
val encode_con : DirPath.t -> Id.t -> Constant.t
val decode_con : Constant.t -> DirPath.t * Id.t

(** {6 Popping one level of section in global names } *)

val pop_con : Constant.t -> Constant.t
val pop_kn : MutInd.t-> MutInd.t
val pop_global_reference : global_reference -> global_reference

(** {6 Global reference is a kernel side type for all references together } *)
type global_reference = Names.global_reference =
  | VarRef of variable           (** A reference to the section-context. *)
  | ConstRef of Constant.t       (** A reference to the environment. *)
  | IndRef of inductive          (** A reference to an inductive type. *)
  | ConstructRef of constructor  (** A reference to a constructor of an inductive type. *)
[@@ocaml.deprecated "Alias of Names.global_reference"]
