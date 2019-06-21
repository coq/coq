(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module registers tables for some non-logical informations
     associated declarations *)

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
(** Kinds used in proofs *)

type goal_object_kind =
  | DefinitionBody of definition_object_kind
  | Proof of theorem_kind

(** Kinds used in library *)

type logical_kind =
  | IsPrimitive
  | IsAssumption of assumption_object_kind
  | IsDefinition of definition_object_kind
  | IsProof of theorem_kind

let logical_kind_of_goal_kind = function
  | DefinitionBody d -> IsDefinition d
  | Proof s -> IsProof s

(** Data associated to section variables and local definitions *)

type variable_data =
  { path:DirPath.t
  ; opaque:bool
  ; univs:Univ.ContextSet.t
  ; poly:bool
  ; kind:logical_kind
  }

let vartab =
  Summary.ref (Id.Map.empty : variable_data Id.Map.t) ~name:"VARIABLE"

let add_variable_data id o = vartab := Id.Map.add id o !vartab

let variable_path id = let {path} = Id.Map.find id !vartab in path
let variable_opacity id = let {opaque} = Id.Map.find id !vartab in opaque
let variable_kind id = let {kind} = Id.Map.find id !vartab in kind
let variable_context id = let {univs} = Id.Map.find id !vartab in univs
let variable_polymorphic id = let {poly} = Id.Map.find id !vartab in poly

let variable_secpath id =
  let dir = drop_dirpath_prefix (Lib.library_dp()) (variable_path id) in
  make_qualid dir id

let variable_exists id = Id.Map.mem id !vartab
