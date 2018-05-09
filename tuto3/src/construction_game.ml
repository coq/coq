open Pp

let example_sort evd =
(* creating a new sort requires that universes should be recorded
  in the evd datastructure, so this datastructure also needs to be
  passed around. *)
  let evd, s = Evd.new_sort_variable Evd.univ_rigid evd in
  let new_type = EConstr.mkSort s in
  evd, new_type

let c_one () =
(* What happens in constructing a new natural number from the datatype
   constructors does not require any handling of existential variables
   or universes, so evd datastructures don't appear here. *)
  let gr_S =
    Coqlib.find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "S" in
(* the long name of "S" was found with the command "About S." *)
  let gr_O =
    Coqlib.find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "O" in
  let c_O = EConstr.of_constr (Universes.constr_of_global gr_O) in
  let c_S = EConstr.of_constr (Universes.constr_of_global gr_S) in
(* Here is the construction of a new term by applying functions to argument. *)
  EConstr.mkApp (c_S, [| c_O |])

let dangling_identity env evd =
(* I call this a dangling identity, because it is not polymorph, but
   the type on which it applies is left unspecified, as it is
   represented by an existential variable.  The declaration for this
   existential variable needs to be added in the evd datastructure. *)
  let evd, type_type = example_sort evd in
  let evd, arg_type = Evarutil.new_evar env evd type_type in
(* Notice the use of a De Bruijn index for the inner occurrence of the
  bound variable. *)
  evd, EConstr.mkLambda(Names.Name (Names.Id.of_string "x"), arg_type,
          EConstr.mkRel 1)

let dangling_identity2 env evd =
(* This example uses directly a function that produces an evar that
  is meant to be a type. *)
  let evd, (arg_type, type_type) =
    Evarutil.new_type_evar env evd Evd.univ_rigid in
  evd, EConstr.mkLambda(Names.Name (Names.Id.of_string "x"), arg_type,
          EConstr.mkRel 1)

let example_sort_app_lambda () =
(* Next, I wish to construct a lambda-abstraction without giving precisely
   the type for the abstracted variable. *)
    let env = Global.env () in
    let evd = Evd.from_env env in
    let c_v = c_one () in
    let evd, c_f = dangling_identity env evd in
    let c_1 = EConstr.mkApp (c_f, [| c_v |]) in
    let _ = Feedback.msg_notice
       (Termops.print_constr_env env evd c_1) in
    (* type verification happens here.  Type verification will update
       existential variable information in the evd part. *)
    let evd, the_type =
      Typing.type_of (Global.env()) evd c_1 in
(* At display time, you will notice that the system knows about the
  existential variable being instantiated to the "nat" type, even
  though c_1 still contains the meta-variable. *)
    Feedback.msg_notice
      ((Termops.print_constr_env env evd c_1) ++
       str " has type " ++
       (Termops.print_constr_env env evd the_type))