(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util
open Libnames

(* Informal mathematical status of declarations *)

type locality =
  | Local
  | Global

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

(* [assumption_kind]

                |  Local      | Global
   ------------------------------------
   Definitional |  Variable   | Parameter
   Logical      |  Hypothesis | Axiom

*)
type assumption_kind = locality * assumption_object_kind

type definition_kind = locality * definition_object_kind

(* Kinds used in proofs *)

type goal_object_kind =
  | DefinitionBody of definition_object_kind
  | Proof of theorem_kind

type goal_kind = locality * goal_object_kind

(* Kinds used in library *)

type logical_kind =
  | IsAssumption of assumption_object_kind
  | IsDefinition of definition_object_kind
  | IsProof of theorem_kind

(* Utils *)

let logical_kind_of_goal_kind = function
  | DefinitionBody d -> IsDefinition d
  | Proof s -> IsProof s

let string_of_theorem_kind = function
  | Theorem -> "Theorem"
  | Lemma -> "Lemma"
  | Fact -> "Fact"
  | Remark -> "Remark"
  | Property -> "Property"
  | Proposition -> "Proposition"
  | Corollary -> "Corollary"

let string_of_definition_kind def =
  match def with
  | Local, Coercion -> "Coercion Local"
  | Global, Coercion -> "Coercion"
  | Local, Definition -> "Let"
  | Global, Definition -> "Definition"
  | Local, SubClass -> "Local SubClass"
  | Global, SubClass -> "SubClass"
  | Global, CanonicalStructure -> "Canonical Structure"
  | Global, Example -> "Example"
  | Local, (CanonicalStructure|Example) ->
      anomaly "Unsupported local definition kind"
  | Local, Instance -> "Instance"
  | Global, Instance -> "Global Instance"
  | _, (StructureComponent|Scheme|CoFixpoint|Fixpoint|IdentityCoercion|Method)
      -> anomaly "Internal definition kind"

(* Strength *)

let strength_of_global = function
  | VarRef _ -> Local
  | IndRef _ | ConstructRef _ | ConstRef _ -> Global

let string_of_strength = function
  | Local -> "Local"
  | Global -> "Global"


(* Recursive power *)

(* spiwack: this definition might be of use in the kernel, for now I do not
                   push them deeper than needed, though. *)
type recursivity_kind =
  | Finite (* = inductive *)
  | CoFinite (* = coinductive *)
  | BiFinite (* = non-recursive, like in "Record" definitions *)

(* helper, converts to "finiteness flag" booleans *)
let recursivity_flag_of_kind = function
  | Finite | BiFinite -> true
  | CoFinite -> false
