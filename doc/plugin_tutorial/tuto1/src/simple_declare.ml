let edeclare ?hook ~name ~poly ~scope ~kind ~opaque sigma udecl body tyopt imps =
  let sigma, ce = DeclareDef.prepare_definition ~allow_evars:false
      ~opaque ~poly sigma udecl ~types:tyopt ~body in
  let uctx = Evd.evar_universe_context sigma in
  let ubinders = Evd.universe_binders sigma in
  let hook_data = Option.map (fun hook -> hook, uctx, []) hook in
  DeclareDef.declare_definition ~name ~scope ~kind ubinders ce imps ?hook_data

let declare_definition ~poly name sigma body =
  let udecl = UState.default_univ_decl in
  edeclare ~name ~poly ~scope:(DeclareDef.Global Declare.ImportDefaultBehavior)
    ~kind:Decl_kinds.Definition ~opaque:false sigma udecl body None []
