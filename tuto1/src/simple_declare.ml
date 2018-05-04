let edeclare ident (_, poly, _ as k) ~opaque sigma udecl body tyopt imps hook =
  let open EConstr in
  let env = Global.env () in
  let sigma = Evd.minimize_universes sigma in
  let body = to_constr sigma body in
  let tyopt = Option.map (to_constr sigma) tyopt in
  let uvars_fold uvars c =
    Univ.LSet.union uvars (Univops.universes_of_constr env c) in
  let uvars = List.fold_left uvars_fold Univ.LSet.empty
     (Option.List.cons tyopt [body]) in
  let sigma = Evd.restrict_universe_context sigma uvars in
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  let ubinders = Evd.universe_binders sigma in
  let ce = Declare.definition_entry ?types:tyopt ~univs body in
  DeclareDef.declare_definition ident k ce ubinders imps hook

let packed_declare_definition ident value_with_constraints =
  let body, ctx = value_with_constraints in
  let sigma = Evd.from_ctx ctx in
  let k = (Decl_kinds.Global,
           Flags.is_universe_polymorphism(), Decl_kinds.Definition) in
  let udecl = Univdecls.default_univ_decl in
  let nohook = Lemmas.mk_hook (fun _ x -> x) in
  ignore (edeclare ident k ~opaque:false sigma udecl body None [] nohook)

(* But this definition cannot be undone by Reset ident *)