(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(* Informal mathematical status of declarations *)

(* Kinds used at parsing time *)

type theorem_kind =
  | Theorem
  | Lemma
  | Fact
  | Remark

type definitionkind =
  | LDefinition
  | GDefinition
  | LCoercion
  | GCoercion
  | LSubClass
  | GSubClass
  | SCanonical

type locality_flag = (*bool (* local = true; global = false *)*)
  | Local
  | Global

type strength = locality_flag (* For compatibility *)

type type_as_formula_kind = Definitional | Logical

(* [assumption_kind] 

                |  Local      | Global
   ------------------------------------
   Definitional |  Variable   | Parameter
   Logical      |  Hypothesis | Axiom
*)
type assumption_kind = locality_flag * type_as_formula_kind

type definition_kind = locality_flag

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
  | IsProof of 'a

type global_kind = theorem_kind mathematical_kind
type local_kind = local_theorem_kind mathematical_kind

(* Utils *)

let theorem_kind_of_goal_kind = function
  | DefinitionBody -> IsDefinition
  | Proof s -> IsProof s

