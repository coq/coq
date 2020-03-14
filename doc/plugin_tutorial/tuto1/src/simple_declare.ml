let edeclare ?hook ~name ~poly ~scope ~kind ~opaque ~udecl ~impargs sigma body tyopt  =
  let sigma, ce = DeclareDef.prepare_definition
      ~opaque ~poly sigma ~udecl ~types:tyopt ~body in
  let uctx = Evd.evar_universe_context sigma in
  let ubind = Evd.universe_binders sigma in
  let hook_data = Option.map (fun hook -> hook, uctx, []) hook in
  DeclareDef.declare_definition ~name ~scope ~kind ~ubind ce ~impargs ?hook_data

let declare_definition ~poly name sigma body =
  let udecl = UState.default_univ_decl in
  edeclare ~name ~poly ~scope:(DeclareDef.Global Declare.ImportDefaultBehavior)
    ~kind:Decls.(IsDefinition Definition) ~opaque:false ~impargs:[] ~udecl sigma body None
