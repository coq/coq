(* A more advanced example of how to explore the structure of terms of
  type constr is given in the coq-dpdgraph plugin. *)

let simple_body_access ~opaque_access gref =
  let open Names.GlobRef in
  match gref with
  | VarRef _ ->
    failwith "variables are not covered in this example"
  | IndRef _ ->
    failwith "inductive types are not covered in this example"
  | ConstructRef _ ->
    failwith "constructors are not covered in this example"
  | ConstRef cst ->
    let cb = Environ.lookup_constant cst (Global.env()) in
    (* most commands should not use body_of_constant_body and opaque accessors,
       but for printing it's ok *)
    match Global.body_of_constant_body opaque_access cb with
    | Some(e, _, _) -> EConstr.of_constr e
    | None -> failwith "This term has no value"

