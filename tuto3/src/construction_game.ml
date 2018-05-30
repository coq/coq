open Pp

let example_sort evd =
(* creating a new sort requires that universes should be recorded
  in the evd datastructure, so this datastructure also needs to be
  passed around. *)
  let evd, s = Evd.new_sort_variable Evd.univ_rigid evd in
  let new_type = EConstr.mkSort s in
  evd, new_type

let c_one evd =
(* In the general case, global references may refer to universe polymorphic
   objects, and their universe has to be made afresh when creating an instance. *)
  let gr_S =
    Coqlib.find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "S" in
(* the long name of "S" was found with the command "About S." *)
  let gr_O =
    Coqlib.find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "O" in
  let evd, c_O = Evarutil.new_global evd gr_O in
  let evd, c_S = Evarutil.new_global evd gr_S in
(* Here is the construction of a new term by applying functions to argument. *)
  evd, EConstr.mkApp (c_S, [| c_O |])

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
    let evd, c_v = c_one evd in
(* dangling_identity and dangling_identity2 can be used interchangeably here *)
    let evd, c_f = dangling_identity2 env evd in
    let c_1 = EConstr.mkApp (c_f, [| c_v |]) in
    let _ = Feedback.msg_notice
       (Termops.print_constr_env env evd c_1) in
    (* type verification happens here.  Type verification will update
       existential variable information in the evd part. *)
    let evd, the_type = Typing.type_of env evd c_1 in
(* At display time, you will notice that the system knows about the
  existential variable being instantiated to the "nat" type, even
  though c_1 still contains the meta-variable. *)
    Feedback.msg_notice
      ((Termops.print_constr_env env evd c_1) ++
       str " has type " ++
       (Termops.print_constr_env env evd the_type))


let c_S evd =
  let gr = Coqlib.find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "S" in
  Evarutil.new_global evd gr

let c_O evd =
  let gr = Coqlib.find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "O" in
  Evarutil.new_global evd gr

let c_E evd =
  let gr = Coqlib.find_reference "Tuto3" ["Tuto3"; "Data"] "EvenNat" in
  Evarutil.new_global evd gr

let c_D evd =
  let gr = Coqlib.find_reference "Tuto3" ["Tuto3"; "Data"] "tuto_div2" in
  Evarutil.new_global evd gr

let c_Q evd =
  let gr = Coqlib.find_reference "Tuto3" ["Coq"; "Init"; "Logic"] "eq" in
  Evarutil.new_global evd gr

let c_R evd =
  let gr = Coqlib.find_reference "Tuto3" ["Coq"; "Init"; "Logic"] "eq_refl" in
  Evarutil.new_global evd gr

let c_N evd =
  let gr = Coqlib.find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "nat" in
  Evarutil.new_global evd gr

let c_C evd =
  let gr = Coqlib.find_reference "Tuto3" ["Tuto3"; "Data"] "C" in
  Evarutil.new_global evd gr

let c_F evd =
  let gr = Coqlib.find_reference "Tuto3" ["Tuto3"; "Data"] "S_ev" in
  Evarutil.new_global evd gr

let c_P evd =
  let gr = Coqlib.find_reference "Tuto3" ["Tuto3"; "Data"] "s_half_proof" in
  Evarutil.new_global evd gr

(* If c_S was universe polymorphic, we should have created a new constant
   at each iteration of buildup. *)
let mk_nat evd n =
  let evd, c_S = c_S evd in
  let evd, c_O = c_O evd in
  let rec buildup = function
    | 0 -> c_O
    | n -> EConstr.mkApp (c_S, [| buildup (n - 1) |]) in
  if n <= 0 then evd, c_O else evd, buildup n

let example_classes n =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let evd, c_n = mk_nat evd n in
  let evd, n_half = mk_nat evd (n / 2) in
  let evd, c_N = c_N evd in
  let evd, c_div = c_D evd in
  let evd, c_even = c_E evd in
  let evd, c_Q = c_Q evd in
  let evd, c_R = c_R evd in
  let arg_type = EConstr.mkApp (c_even, [| c_n |]) in
  let evd0 = evd in
  let evd, instance = Evarutil.new_evar env evd arg_type in
  let c_half = EConstr.mkApp (c_div, [|c_n; instance|]) in
  let _ = Feedback.msg_notice (Termops.print_constr_env env evd c_half) in
  let evd, the_type = Typing.type_of env evd c_half in
  let _ = Feedback.msg_notice (Termops.print_constr_env env evd c_half) in
  let proved_equality =
    EConstr.mkCast(EConstr.mkApp (c_R, [| c_N; c_half |]), Constr.DEFAULTcast,
      EConstr.mkApp (c_Q, [| c_N; c_half; n_half|])) in
(* This is where we force the system to compute with type classes. *)
(* Question to coq developers: why do we pass two evd arguments to
   solve_remaining_evars? Is the choice of evd0 relevant here? *)
  let evd = Pretyping.solve_remaining_evars
    (Pretyping.default_inference_flags true) env evd evd0 in
  let evd, final_type = Typing.type_of env evd proved_equality in
  Feedback.msg_notice (Termops.print_constr_env env evd proved_equality)

(* This function, together with definitions in Data.v, shows how to
   trigger automatic proofs at the time of typechecking, based on
   canonical structures.

   n is a number for which we want to find the half (and a proof that
   this half is indeed the half)
*)
let example_canonical n =
  let env = Global.env () in
  let evd = Evd.from_env env in
(* Construct a natural representation of this integer. *)
  let evd, c_n = mk_nat evd n in
(* terms for "nat", "eq", "S_ev", "eq_refl", "C" *)
  let evd, c_N = c_N evd in
  let evd, c_F = c_F evd in
  let evd, c_R = c_R evd in
  let evd, c_C = c_C evd in
  let evd, c_P = c_P evd in
(* the last argument of C *)
  let refl_term = EConstr.mkApp (c_R, [|c_N; c_n |]) in
(* Now we build two existential variables, for the value of the half and for
   the "S_ev" structure that triggers the proof search. *)
  let evd, ev1 = Evarutil.new_evar env evd c_N in
(* This is the type for the second existential variable *)
  let csev = EConstr.mkApp (c_F, [| ev1 |]) in
  let evd, ev2 = Evarutil.new_evar env evd csev in
(* Now we build the C structure. *)
  let test_term = EConstr.mkApp (c_C, [| c_n; ev1; ev2; refl_term |]) in
(* Type-checking this term will compute values for the existential variables *)
  let evd, final_type = Typing.type_of env evd test_term in
(* The computed type has two parameters, the second one is the proof. *)
  let value = match EConstr.kind evd final_type with
      | Constr.App(_, [| _; the_half |]) -> the_half
      | _ -> failwith "expecting the whole type to be \"cmp _ the_half\"" in
  let _ = Feedback.msg_notice (Termops.print_constr_env env evd value) in
(* I wish for a nicer way to get the value of ev2 in the evar_map *)
  let prf_struct = EConstr.of_constr (EConstr.to_constr evd ev2) in
  let the_prf = EConstr.mkApp (c_P, [| ev1; prf_struct |]) in
  let evd, the_statement = Typing.type_of env evd the_prf in
  Feedback.msg_notice
    (Termops.print_constr_env env evd the_prf ++ str " has type " ++
     Termops.print_constr_env env evd the_statement)
