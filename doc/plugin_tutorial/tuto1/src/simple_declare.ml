let edeclare ?hook ident (_, poly, _ as k) ~opaque sigma udecl body tyopt imps =
  let sigma, ce = DeclareDef.prepare_definition ~allow_evars:false
      ~opaque ~poly sigma udecl ~types:tyopt ~body in
  let uctx = Evd.evar_universe_context sigma in
  let ubinders = Evd.universe_binders sigma in
  let hook_data = Option.map (fun hook -> hook, uctx, []) hook in
  DeclareDef.declare_definition ident k ce ubinders imps ?hook_data

let declare_definition ~poly ident sigma body =
  let k = Decl_kinds.(Global ImportDefaultBehavior, poly, Definition) in
  let udecl = UState.default_univ_decl in
  edeclare ident k ~opaque:false sigma udecl body None []

(* But this definition cannot be undone by Reset ident *)
