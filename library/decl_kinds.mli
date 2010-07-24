(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Libnames

(** Informal mathematical status of declarations *)

type locality =
  | Local
  | Global

type boxed_flag = bool

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

type assumption_object_kind = Definitional | Logical | Conjectural

(** [assumption_kind]

                |  Local      | Global
   ------------------------------------
   Definitional |  Variable   | Parameter
   Logical      |  Hypothesis | Axiom

*)
type assumption_kind = locality * assumption_object_kind

type definition_kind = locality * boxed_flag * definition_object_kind

(** Kinds used in proofs *)

type goal_object_kind =
  | DefinitionBody of definition_object_kind
  | Proof of theorem_kind

type goal_kind = locality * goal_object_kind

(** Kinds used in library *)

type logical_kind =
  | IsAssumption of assumption_object_kind
  | IsDefinition of definition_object_kind
  | IsProof of theorem_kind

(** Utils *)

val logical_kind_of_goal_kind : goal_object_kind -> logical_kind
val string_of_theorem_kind : theorem_kind -> string
val string_of_definition_kind :
  locality * boxed_flag * definition_object_kind -> string

(** About locality *)

val strength_of_global : global_reference -> locality
val string_of_strength : locality -> string

(** About recursive power of type declarations *)

type recursivity_kind =
  | Finite (** = inductive *)
  | CoFinite (** = coinductive *)
  | BiFinite (** = non-recursive, like in "Record" definitions *)

(** helper, converts to "finiteness flag" booleans *)
val recursivity_flag_of_kind : recursivity_kind -> bool
