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

type theorem_kind =
  | Theorem
  | Lemma
  | Fact
  | Remark
  | Property
  | Proposition
  | Corollary

type definition_object_kind =
  | Definition
  | Coercion
  | SubClass
  | CanonicalStructure
  | Example
  | Fixpoint
  | CoFixpoint
  | Scheme
  | StructureComponent
  | IdentityCoercion
  | Instance
  | Method
  | Let

type assumption_object_kind = Definitional | Logical | Conjectural | Context

(* [assumption_kind]

                |  Local      | Global
   ------------------------------------
   Definitional |  Variable   | Parameter
   Logical      |  Hypothesis | Axiom

*)

(** Kinds used in library *)

type logical_kind =
  | IsPrimitive
  | IsAssumption of assumption_object_kind
  | IsDefinition of definition_object_kind
  | IsProof of theorem_kind

(** This module manages non-kernel informations about declarations. It
    is either non-logical informations or logical informations that
    have no place to be (yet) in the kernel *)

(** Registration and access to the table of variable *)

type variable_data = {
  opaque:bool;
  kind:logical_kind;
}

val add_variable_data : variable -> variable_data -> unit

(* Only used in dumpglob *)
val variable_secpath : variable -> qualid
val variable_kind : variable -> logical_kind

(* User in Lemma, Very dubious *)
val variable_opacity : variable -> bool

(* Used in declare, very dubious *)
val variable_exists : variable -> bool
