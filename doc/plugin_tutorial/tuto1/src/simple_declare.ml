let edeclare ?hook ~ontop ident (_, poly, _ as k) ~opaque sigma udecl body tyopt imps =
  let sigma, ce = DeclareDef.prepare_definition ~allow_evars:false
      ~opaque ~poly sigma udecl ~types:tyopt ~body in
  let uctx = Evd.evar_universe_context sigma in
  let ubinders = Evd.universe_binders sigma in
  let hook_data = Option.map (fun hook -> hook, uctx, []) hook in
  DeclareDef.declare_definition ~ontop ident k ce ubinders imps ?hook_data

let packed_declare_definition ~poly ident value_with_constraints =
  let body, ctx = value_with_constraints in
  let sigma = Evd.from_ctx ctx in
  let k = (Decl_kinds.Global, poly, Decl_kinds.Definition) in
  let udecl = UState.default_univ_decl in
  ignore (edeclare ~ontop:None ident k ~opaque:false sigma udecl body None [])

(* But this definition cannot be undone by Reset ident *)
