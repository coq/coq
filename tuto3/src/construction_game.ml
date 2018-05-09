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
    let env = Global.env () in
    let evd = Evd.from_env env in
    let c_v = c_one () in
(* dangling_identity and dangling_identity2 can be used interchangeably here *)
    let evd, c_f = dangling_identity2 env evd in
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

let constants = ref ([] : EConstr.constr list)

let collect_constants () =
  if (!constants = []) then
    let open Coqlib in
    let open EConstr in
    let open Universes in
    let gr_S = find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "S" in
    let gr_O = find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "O" in
    let gr_E = find_reference "Tuto3" ["Tuto3"; "Data"] "EvenNat" in
    let gr_D = find_reference "Tuto3" ["Tuto3"; "Data"] "tuto_div2" in
    constants := List.map (fun x -> of_constr (constr_of_global x))
      [gr_S; gr_O; gr_E; gr_D];
    !constants
  else
    !constants

let c_S () =
  match collect_constants () with
    it :: _ -> it
  | _ -> failwith "could not obtain an internal representation of S : nat"

let c_O () =
  match collect_constants () with
    _ :: it :: _ -> it
  | _ -> failwith "could not obtain an internal representation of 0 : nat"

let c_E () =
  match collect_constants () with
    _ :: _ :: it :: _ -> it
  | _ -> failwith "could not obtain an internal representation of EvenNat"

let c_D () =
  match collect_constants () with
    _ :: _ :: _ :: it :: _ -> it
  | _ -> failwith "could not obtain an internal representation of tuto_div2"

let mk_nat n =
  let c_S = c_S () in  
  let c_O = c_O () in
  let rec buildup = function
    | 0 -> c_O
    | n -> EConstr.mkApp (c_S, [| buildup (n - 1) |]) in
  if n <= 0 then c_O else buildup n

let example_classes n =
  let c_n = mk_nat n in
  let c_div = c_D () in
  let c_even = c_E () in
  let arg_type = EConstr.mkApp (c_even, [| c_n |]) in
  let env = Global.env () in
  let evd = Evd.from_env env in
  let evd, instance = Evarutil.new_evar env evd arg_type in
  let c_1 = EConstr.mkApp (c_div, [|c_n; instance|]) in
  let _ = Feedback.msg_notice (Termops.print_constr_env env evd c_1) in
  let evd, the_type = Typing.type_of env evd c_1 in
  Feedback.msg_notice (Termops.print_constr_env env evd c_1)