(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Informal mathematical status of declarations *)

type locality = Discharge | Local | Global

type implicit_status = Explicit | Implicit

type binding_kind = implicit_status
(** @deprecated Alias type *)

type polymorphic = bool

type private_flag = bool 

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
type 'a declaration_kind = { locality : locality;
                             polymorphic : bool;
                             object_kind : 'a }

type assumption_kind = assumption_object_kind declaration_kind

type definition_kind = definition_object_kind declaration_kind

(** Kinds used in proofs *)

type goal_object_kind =
  | DefinitionBody of definition_object_kind
  | Proof of theorem_kind

type goal_kind = goal_object_kind declaration_kind

(** Kinds used in library *)

type logical_kind =
  | IsAssumption of assumption_object_kind
  | IsDefinition of definition_object_kind
  | IsProof of theorem_kind

(** Recursive power of type declarations *)

type recursivity_kind =
  | Finite (** = inductive *)
  | CoFinite (** = coinductive *)
  | BiFinite (** = non-recursive, like in "Record" definitions *)
