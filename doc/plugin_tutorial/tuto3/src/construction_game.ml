open Pp
open Context

let find_reference = Coqlib.find_reference [@ocaml.warning "-3"]

let example_sort sigma =
(* creating a new sort requires that universes should be recorded
  in the evd datastructure, so this datastructure also needs to be
  passed around. *)
  let sigma, s = Evd.new_sort_variable Evd.univ_rigid sigma in
  let new_type = EConstr.mkSort s in
  sigma, new_type

let c_one sigma =
(* In the general case, global references may refer to universe polymorphic
   objects, and their universe has to be made afresh when creating an instance. *)
  let gr_S =
    find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "S" in
(* the long name of "S" was found with the command "About S." *)
  let gr_O =
    find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "O" in
  let sigma, c_O = Evarutil.new_global sigma gr_O in
  let sigma, c_S = Evarutil.new_global sigma gr_S in
(* Here is the construction of a new term by applying functions to argument. *)
  sigma, EConstr.mkApp (c_S, [| c_O |])

let dangling_identity env sigma =
(* I call this a dangling identity, because it is not polymorph, but
   the type on which it applies is left unspecified, as it is
   represented by an existential variable.  The declaration for this
   existential variable needs to be added in the evd datastructure. *)
  let sigma, type_type = example_sort sigma in
  let sigma, arg_type = Evarutil.new_evar env sigma type_type in
(* Notice the use of a De Bruijn index for the inner occurrence of the
  bound variable. *)
  sigma, EConstr.mkLambda(nameR (Names.Id.of_string "x"), arg_type,
          EConstr.mkRel 1)

let dangling_identity2 env sigma =
(* This example uses directly a function that produces an evar that
  is meant to be a type. *)
  let sigma, (arg_type, type_type) =
    Evarutil.new_type_evar env sigma Evd.univ_rigid in
  sigma, EConstr.mkLambda(nameR (Names.Id.of_string "x"), arg_type,
          EConstr.mkRel 1)

let example_sort_app_lambda () =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let sigma, c_v = c_one sigma in
(* dangling_identity and dangling_identity2 can be used interchangeably here *)
    let sigma, c_f = dangling_identity2 env sigma in
    let c_1 = EConstr.mkApp (c_f, [| c_v |]) in
    let _ = Feedback.msg_notice
       (Printer.pr_econstr_env env sigma c_1) in
    (* type verification happens here.  Type verification will update
       existential variable information in the evd part. *)
    let sigma, the_type = Typing.type_of env sigma c_1 in
(* At display time, you will notice that the system knows about the
  existential variable being instantiated to the "nat" type, even
  though c_1 still contains the meta-variable. *)
    Feedback.msg_notice
      ((Printer.pr_econstr_env env sigma c_1) ++
       str " has type " ++
       (Printer.pr_econstr_env env sigma the_type))


let c_S sigma =
  let gr = find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "S" in
  Evarutil.new_global sigma gr

let c_O sigma =
  let gr = find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "O" in
  Evarutil.new_global sigma gr

let c_E sigma =
  let gr = find_reference "Tuto3" ["Tuto3"; "Data"] "EvenNat" in
  Evarutil.new_global sigma gr

let c_D sigma =
  let gr = find_reference "Tuto3" ["Tuto3"; "Data"] "tuto_div2" in
  Evarutil.new_global sigma gr

let c_Q sigma =
  let gr = find_reference "Tuto3" ["Coq"; "Init"; "Logic"] "eq" in
  Evarutil.new_global sigma gr

let c_R sigma =
  let gr = find_reference "Tuto3" ["Coq"; "Init"; "Logic"] "eq_refl" in
  Evarutil.new_global sigma gr

let c_N sigma =
  let gr = find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "nat" in
  Evarutil.new_global sigma gr

let c_C sigma =
  let gr = find_reference "Tuto3" ["Tuto3"; "Data"] "C" in
  Evarutil.new_global sigma gr

let c_F sigma =
  let gr = find_reference "Tuto3" ["Tuto3"; "Data"] "S_ev" in
  Evarutil.new_global sigma gr

let c_P sigma =
  let gr = find_reference "Tuto3" ["Tuto3"; "Data"] "s_half_proof" in
  Evarutil.new_global sigma gr

(* If c_S was universe polymorphic, we should have created a new constant
   at each iteration of buildup. *)
let mk_nat sigma n =
  let sigma, c_S = c_S sigma in
  let sigma, c_O = c_O sigma in
  let rec buildup = function
    | 0 -> c_O
    | n -> EConstr.mkApp (c_S, [| buildup (n - 1) |]) in
  if n <= 0 then sigma, c_O else sigma, buildup n

let example_classes n =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, c_n = mk_nat sigma n in
  let sigma, n_half = mk_nat sigma (n / 2) in
  let sigma, c_N = c_N sigma in
  let sigma, c_div = c_D sigma in
  let sigma, c_even = c_E sigma in
  let sigma, c_Q = c_Q sigma in
  let sigma, c_R = c_R sigma in
  let arg_type = EConstr.mkApp (c_even, [| c_n |]) in
  let sigma0 = sigma in
  let sigma, instance = Evarutil.new_evar env sigma arg_type in
  let c_half = EConstr.mkApp (c_div, [|c_n; instance|]) in
  let _ = Feedback.msg_notice (Printer.pr_econstr_env env sigma c_half) in
  let sigma, the_type = Typing.type_of env sigma c_half in
  let _ = Feedback.msg_notice (Printer.pr_econstr_env env sigma c_half) in
  let proved_equality =
    EConstr.mkCast(EConstr.mkApp (c_R, [| c_N; c_half |]), Constr.DEFAULTcast,
      EConstr.mkApp (c_Q, [| c_N; c_half; n_half|])) in
(* This is where we force the system to compute with type classes. *)
(* Question to coq developers: why do we pass two evd arguments to
   solve_remaining_evars? Is the choice of sigma0 relevant here? *)
  let sigma = Pretyping.solve_remaining_evars
    (Pretyping.default_inference_flags true) env sigma ~initial:sigma0 in
  let sigma, final_type = Typing.type_of env sigma proved_equality in
  Feedback.msg_notice (Printer.pr_econstr_env env sigma proved_equality)

(* This function, together with definitions in Data.v, shows how to
   trigger automatic proofs at the time of typechecking, based on
   canonical structures.

   n is a number for which we want to find the half (and a proof that
   this half is indeed the half)
*)
let example_canonical n =
  let env = Global.env () in
  let sigma = Evd.from_env env in
(* Construct a natural representation of this integer. *)
  let sigma, c_n = mk_nat sigma n in
(* terms for "nat", "eq", "S_ev", "eq_refl", "C" *)
  let sigma, c_N = c_N sigma in
  let sigma, c_F = c_F sigma in
  let sigma, c_R = c_R sigma in
  let sigma, c_C = c_C sigma in
  let sigma, c_P = c_P sigma in
(* the last argument of C *)
  let refl_term = EConstr.mkApp (c_R, [|c_N; c_n |]) in
(* Now we build two existential variables, for the value of the half and for
   the "S_ev" structure that triggers the proof search. *)
  let sigma, ev1 = Evarutil.new_evar env sigma c_N in
(* This is the type for the second existential variable *)
  let csev = EConstr.mkApp (c_F, [| ev1 |]) in
  let sigma, ev2 = Evarutil.new_evar env sigma csev in
(* Now we build the C structure. *)
  let test_term = EConstr.mkApp (c_C, [| c_n; ev1; ev2; refl_term |]) in
(* Type-checking this term will compute values for the existential variables *)
  let sigma, final_type = Typing.type_of env sigma test_term in
(* The computed type has two parameters, the second one is the proof. *)
  let value = match EConstr.kind sigma final_type with
      | Constr.App(_, [| _; the_half |]) -> the_half
      | _ -> failwith "expecting the whole type to be \"cmp _ the_half\"" in
  let _ = Feedback.msg_notice (Printer.pr_econstr_env env sigma value) in
(* I wish for a nicer way to get the value of ev2 in the evar_map *)
  let prf_struct = EConstr.of_constr (EConstr.to_constr sigma ev2) in
  let the_prf = EConstr.mkApp (c_P, [| ev1; prf_struct |]) in
  let sigma, the_statement = Typing.type_of env sigma the_prf in
  Feedback.msg_notice
    (Printer.pr_econstr_env env sigma the_prf ++ str " has type " ++
     Printer.pr_econstr_env env sigma the_statement)
