let edeclare ?hook ~name ~poly ~scope ~kind ~opaque ~udecl ~impargs sigma body tyopt  =
  let ce = DeclareDef.prepare_definition
      ~opaque ~poly sigma ~udecl ~types:tyopt ~body in
  DeclareDef.declare_definition ~name ~scope ~kind ~impargs ?hook ce

let declare_definition ~poly name sigma body =
  let udecl = UState.default_univ_decl in
  edeclare ~name ~poly ~scope:(DeclareDef.Global Declare.ImportDefaultBehavior)
    ~kind:Decls.(IsDefinition Definition) ~opaque:false ~impargs:[] ~udecl sigma body None
