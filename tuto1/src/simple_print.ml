let simple_body_access gref =
  match gref with
  | Globnames.VarRef _ ->
    failwith "variables are not covered in this example"
  | Globnames.IndRef _ ->
    failwith "inductive types are not covered in this example"
  | Globnames.ConstructRef _ ->
    failwith "constructors are not covered in this example"
  | Globnames.ConstRef cst ->
    let cb = Environ.lookup_constant cst (Global.env()) in
    match Global.body_of_constant_body cb with
    | Some(e, _) -> e
    | None -> failwith "This term has no value"

