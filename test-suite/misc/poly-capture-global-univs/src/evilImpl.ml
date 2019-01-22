open Names
open Entries
open Univ

let make_entry ?(mono=ContextSet.empty) ?(poly=UContext.empty) () =
  { entry_monomorphic_univs = mono;
    entry_poly_univ_names = Array.make (UContext.size poly) Anonymous;
    entry_polymorphic_univs = poly;
    entry_is_polymorphic = not (UContext.is_empty poly);
  }

let evil t f =
  let open Decl_kinds in
  let open Constr in
  let k = IsDefinition Definition in
  let u = Level.var 0 in
  let tu = mkType (Universe.make u) in
  let te = Declare.definition_entry
      ~univs:(make_entry ~mono:(ContextSet.singleton u) ()) tu
  in
  let tc = Declare.declare_constant t (DefinitionEntry te, k) in
  let tc = mkConst tc in

  let fe = Declare.definition_entry
      ~univs:(make_entry ~poly:(UContext.make (Instance.of_array [|u|],Constraint.empty)) ())
      ~types:(Term.mkArrow tc tu)
      (mkLambda (Name.Name (Id.of_string "x"), tc, mkRel 1))
  in
  ignore (Declare.declare_constant f (DefinitionEntry fe, k))
