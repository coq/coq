(* A more advanced example of how to explore the structure of terms of
  type constr is given in the coq-dpdgraph plugin. *)

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
    match Global.body_of_constant_body Library.indirect_accessor cb with
    | Some(e, _, _) -> EConstr.of_constr e
    | None -> failwith "This term has no value"

