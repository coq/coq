let simple_check value_with_constraints =
  begin
    let evalue, st = value_with_constraints in
    let evd = Evd.from_ctx st in
    let j = Termops.on_judgment EConstr.of_constr
      (Arguments_renaming.rename_typing (Global.env())
         (EConstr.to_constr evd evalue)) in
    let {Environ.uj_type=x}=j in x
  end