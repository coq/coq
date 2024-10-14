(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
  | LetContext

type assumption_object_kind = Definitional | Logical | Conjectural | Context

(* [assumption_kind]

                |  Local      | Global
   ------------------------------------
   Definitional |  Variable   | Parameter
   Logical      |  Hypothesis | Axiom

*)

(** Kinds *)

type logical_kind =
  | IsPrimitive
  | IsSymbol
  | IsAssumption of assumption_object_kind
  | IsDefinition of definition_object_kind
  | IsProof of theorem_kind

(** Data associated to section variables and local definitions *)

type variable_data = {
  opaque:bool;
  kind:logical_kind;
}

let vartab =
  Summary.ref (Id.Map.empty : (variable_data*DirPath.t) Id.Map.t) ~name:"VARIABLE"

let secpath () = drop_dirpath_prefix (Lib.library_dp()) (Lib.cwd())
let add_variable_data id o = vartab := Id.Map.add id (o,secpath()) !vartab

let variable_opacity id = let {opaque},_ = Id.Map.find id !vartab in opaque
let variable_kind id = let {kind},_ = Id.Map.find id !vartab in kind

let variable_secpath id =
  let _, dir = Id.Map.find id !vartab in
  make_qualid dir id

let variable_exists id = Id.Map.mem id !vartab
