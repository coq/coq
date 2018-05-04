let simple_check1 value_with_constraints =
  begin
    let evalue, st = value_with_constraints in
    let evd = Evd.from_ctx st in
(* This is reverse engineered from vernacentries.ml *)
(* The point of renaming is to make sure the bound names printed by Check
   can be re-used in `apply with` tactics that use bound names to
   refer to arguments. *)
    let j = Termops.on_judgment EConstr.of_constr
      (Arguments_renaming.rename_typing (Global.env())
         (EConstr.to_constr evd evalue)) in
    let {Environ.uj_type=x}=j in x
  end

let simple_check2 value_with_constraints =
  let evalue, st = value_with_constraints in
  let evd = Evd.from_ctx st in
(* This version should be preferred if bound variable names are not so
  important, you want to really verify that the input is well-typed,
  and if you want to obtain the type. *)
(* Note that the output value is a pair containing a new evar_map:
   typing will fill out blanks in the term by add evar bindings. *)
  Typing.type_of (Global.env()) evd evalue

let simple_check3 value_with_constraints =
  let evalue, st = value_with_constraints in
  let evd = Evd.from_ctx st in
(* This version should be preferred if bound variable names are not so
  important and you already expect the input to have been type-checked
  before.  Set ~lax to false if you want an anomaly to be raised in
  case of a type error.  Otherwise a ReTypeError exception is raised. *)
  Retyping.get_type_of ~lax:true (Global.env()) evd evalue