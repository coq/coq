(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* Informal mathematical status of declarations *)

type locality_flag = (*bool (* local = true; global = false *)*)
  | Local
  | Global

(* Kinds used at parsing time *)

type theorem_kind =
  | Theorem
  | Lemma
  | Fact
  | Remark

type definition_object_kind =
  | Definition
  | Coercion
  | SubClass
  | CanonicalStructure

type strength = locality_flag (* For compatibility *)

type type_as_formula_kind = Definitional | Logical | Conjectural

(* [assumption_kind] 

                |  Local      | Global
   ------------------------------------
   Definitional |  Variable   | Parameter
   Logical      |  Hypothesis | Axiom

*)
type assumption_kind = locality_flag * type_as_formula_kind

type definition_kind = locality_flag * definition_object_kind

(* Kinds used in proofs *)

type global_goal_kind =
  | DefinitionBody
  | Proof of theorem_kind

type goal_kind =
  | IsGlobal of global_goal_kind
  | IsLocal

(* Kinds used in library *)

type local_theorem_kind = LocalStatement

type 'a mathematical_kind =
  | IsAssumption of type_as_formula_kind
  | IsDefinition
  | IsConjecture
  | IsProof of 'a

type global_kind = theorem_kind mathematical_kind
type local_kind = local_theorem_kind mathematical_kind

(* Utils *)

let theorem_kind_of_goal_kind = function
  | DefinitionBody -> IsDefinition
  | Proof s -> IsProof s

