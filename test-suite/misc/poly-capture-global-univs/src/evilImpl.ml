open Names

let evil t f =
  let open Univ in
  let open Entries in
  let open Decl_kinds in
  let open Constr in
  let k = IsDefinition Definition in
  let u = Level.var 0 in
  let tu = mkType (Universe.make u) in
  let te = Declare.definition_entry
      ~univs:(Monomorphic_const_entry (ContextSet.singleton u)) tu
  in
  let tc = Declare.declare_constant t (DefinitionEntry te, k) in
  let tc = mkConst tc in

  let fe = Declare.definition_entry
      ~univs:(Polymorphic_const_entry (UContext.make (Instance.of_array [|u|],Constraint.empty)))
      ~types:(Term.mkArrow tc tu)
      (mkLambda (Name.Name (Id.of_string "x"), tc, mkRel 1))
  in
  ignore (Declare.declare_constant f (DefinitionEntry fe, k))
