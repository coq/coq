(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Decl_kinds

(** Operations about types defined in [Decl_kinds] *)

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
      Errors.anomaly "Unsupported local definition kind"
  | Local, Instance -> "Instance"
  | Global, Instance -> "Global Instance"
  | _, (StructureComponent|Scheme|CoFixpoint|Fixpoint|IdentityCoercion|Method)
      -> Errors.anomaly "Internal definition kind"
