open Names

let evil name name_f =
  let open Univ in
  let open Entries in
  let open Constr in
  let kind = Decls.(IsDefinition Definition) in
  let u = Level.var 0 in
  let tu = mkType (Universe.make u) in
  let te = Declare.definition_entry
      ~univs:(Monomorphic_entry (ContextSet.singleton u)) tu
  in
  let tc = Declare.declare_constant ~name ~kind (Declare.DefinitionEntry te) in
  let tc = mkConst tc in

  let fe = Declare.definition_entry
      ~univs:(Polymorphic_entry ([|Anonymous|], UContext.make (Instance.of_array [|u|],Constraint.empty)))
      ~types:(Term.mkArrowR tc tu)
      (mkLambda (Context.nameR (Id.of_string "x"), tc, mkRel 1))
  in
  let _ : Constant.t = Declare.declare_constant ~name:name_f ~kind (Declare.DefinitionEntry fe) in
  ()
