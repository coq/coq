(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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
  let (locality, poly, kind) = def in
  let error () = Errors.anomaly (Pp.str "Internal definition kind") in
  match kind with
  | Definition ->
    begin match locality with
    | Discharge -> "Let"
    | Local -> "Local Definition"
    | Global -> "Definition"
    end
  | Example ->
    begin match locality with
    | Discharge -> error ()
    | Local -> "Local Example"
    | Global -> "Example"
    end
  | Coercion ->
    begin match locality with
    | Discharge -> error ()
    | Local -> "Local Coercion"
    | Global -> "Coercion"
    end
  | SubClass ->
    begin match locality with
    | Discharge -> error ()
    | Local -> "Local SubClass"
    | Global -> "SubClass"
    end
  | CanonicalStructure ->
    begin match locality with
    | Discharge -> error ()
    | Local -> error ()
    | Global -> "Canonical Structure"
    end
  | Instance ->
    begin match locality with
    | Discharge -> error ()
    | Local -> "Instance"
    | Global -> "Global Instance"
    end
  | (StructureComponent|Scheme|CoFixpoint|Fixpoint|IdentityCoercion|Method) ->
    Errors.anomaly (Pp.str "Internal definition kind")
