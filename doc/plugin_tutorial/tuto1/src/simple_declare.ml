let declare_definition ~poly name sigma body =
  let udecl = UState.default_univ_decl in
  let scope = Declare.Global Declare.ImportDefaultBehavior in
  let kind = Decls.(IsDefinition Definition) in
  Declare.declare_definition ~name ~scope ~kind ~impargs:[] ~udecl
    ~opaque:false ~poly ~types:None ~body sigma
