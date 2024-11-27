open Names

let evil name name_f =
  let open Univ in
  let open UVars in
  let open Constr in
  let kind = Decls.(IsDefinition Definition) in
  let lu = Level.var 0 in
  let u = Universe.make lu in
  let tu = mkType u in
  let te = Declare.definition_entry
      ~univs:(UState.{ universes_entry_universes = Monomorphic_entry (ContextSet.singleton lu);
        universes_entry_binders = UnivNames.empty_binders }) tu
  in
  let tc = Declare.declare_constant ~name ~kind (Declare.DefinitionEntry te) in
  let tc = UnsafeMonomorphic.mkConst tc in

  let fe = Declare.definition_entry
      ~univs:(UState.(Polymorphic_entry
        { universes_entry_universes = (UContext.make ([||],[|Anonymous|])
            (LevelInstance.of_array ([||],[|lu|]),Constraints.empty));
            universes_entry_binders = UnivNames.empty_binders }))
      ~types:(Term.mkArrowR tc tu)
      (mkLambda (Context.nameR (Id.of_string "x"), tc, mkRel 1))
  in
  let _ : Constant.t = Declare.declare_constant ~name:name_f ~kind (Declare.DefinitionEntry fe) in
  ()
