(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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

let string_of_definition_object_kind = function
  | Definition -> "Definition"
  | Example -> "Example"
  | Coercion -> "Coercion"
  | SubClass -> "SubClass"
  | CanonicalStructure -> "Canonical Structure"
  | Instance -> "Instance"
  | Let -> "Let"
  | (StructureComponent|Scheme|CoFixpoint|Fixpoint|IdentityCoercion|Method) ->
    CErrors.anomaly (Pp.str "Internal definition kind.")
