let packed_declare_definition ident
  (value_with_constraints : EConstr.constr Evd.in_evar_universe_context) =
  begin
    let evalue, st = value_with_constraints in
    let evd = Evd.from_ctx st in
    let value = EConstr.to_constr evd evalue in
(* Question to developers: could the next 3 lines be removed:
   similar stuff present in comDefinition and elpi, but not in Mtac2 *)
    let evd = Evd.minimize_universes evd in
    let used = Univops.universes_of_constr (Global.env()) value in
    let evd = Evd.restrict_universe_context evd used in
    let decl = Univdecls.default_univ_decl in
    let uctx = Evd.check_univ_decl ~poly:true evd decl in
    let ce = Declare.definition_entry ~univs:uctx value in
    let _  =
      Pretyping.check_evars_are_solved (Global.env ()) evd Evd.empty in
    let k = (Decl_kinds.Global,
             true (* polymorphic *), Decl_kinds.Definition) in
    let binders = Evd.universe_binders evd in
    let implicits = [] in
    let hook = Lemmas.mk_hook (fun _ x -> x) in
    ignore(DeclareDef.declare_definition ident k ce binders implicits hook)
  end

(* But this definition cannot be undone by Reset ident *)