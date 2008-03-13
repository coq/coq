(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util

(* Informal mathematical status of declarations *)

type locality_flag = (*bool (* local = true; global = false *)*)
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

type strength = locality_flag (* For compatibility *)

type assumption_object_kind = Definitional | Logical | Conjectural

(* [assumption_kind] 

                |  Local      | Global
   ------------------------------------
   Definitional |  Variable   | Parameter
   Logical      |  Hypothesis | Axiom

*)
type assumption_kind = locality_flag * assumption_object_kind

type definition_kind = locality_flag * boxed_flag * definition_object_kind

(* Kinds of proof enders. *)
type opacity_flag = bool
type lident = Names.identifier located
type proof_end =
  | Admitted
  | Proved of opacity_flag * (lident * theorem_kind option) option

(* Kinds used in proofs *)

type goal_object_kind =
  | DefinitionBody of definition_object_kind
  | Proof of theorem_kind

type goal_kind = locality_flag * goal_object_kind

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

let string_of_definition_kind (l,boxed,d) =
  match (l,d) with
  | Local, Coercion -> "Coercion Local"
  | Global, Coercion -> "Coercion"
  | Local, Definition -> "Let"
  | Global, Definition -> if boxed then "Boxed Definition" else "Definition"
  | Local, SubClass -> "Local SubClass"
  | Global, SubClass -> "SubClass"
  | Global, CanonicalStructure -> "Canonical Structure"
  | Global, Example -> "Example"
  | Local, (CanonicalStructure|Example) ->
      anomaly "Unsupported local definition kind"
  | _, (StructureComponent|Scheme|CoFixpoint|Fixpoint|IdentityCoercion)
      -> anomaly "Internal definition kind"
