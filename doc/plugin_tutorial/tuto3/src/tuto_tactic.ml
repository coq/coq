open Proofview

let constants = ref ([] : EConstr.t list)

(* This is a pattern to collect terms from the Coq memory of valid terms
  and proofs.  This pattern extends all the way to the definition of function
 c_U *)
let collect_constants () =
  if (!constants = []) then
    let open EConstr in
    let open UnivGen in
    let find_reference = Coqlib.find_reference [@ocaml.warning "-3"] in
    let gr_H = find_reference "Tuto3" ["Tuto3"; "Data"] "pack" in
    let gr_M = find_reference "Tuto3" ["Tuto3"; "Data"] "packer" in
    let gr_R = find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "pair" in
    let gr_P = find_reference "Tuto3" ["Coq"; "Init"; "Datatypes"] "prod" in
    let gr_U = find_reference "Tuto3" ["Tuto3"; "Data"] "uncover" in
    constants := List.map (fun x -> of_constr (constr_of_monomorphic_global x))
      [gr_H; gr_M; gr_R; gr_P; gr_U];
    !constants
  else
    !constants

let c_H () =
  match collect_constants () with
    it :: _ -> it
  | _ -> failwith "could not obtain an internal representation of pack"

let c_M () =
  match collect_constants () with
    _ :: it :: _ -> it
  | _ -> failwith "could not obtain an internal representation of pack_marker"

let c_R () =
  match collect_constants () with
    _ :: _ :: it :: _ -> it
  | _ -> failwith "could not obtain an internal representation of pair"

let c_P () =
  match collect_constants () with
    _ :: _ :: _ :: it :: _ -> it
  | _ -> failwith "could not obtain an internal representation of prod"

let c_U () =
  match collect_constants () with
    _ :: _ :: _ :: _ :: it :: _ -> it
  | _ -> failwith "could not obtain an internal representation of prod"

(* The following tactic is meant to pack an hypothesis when no other
   data is already packed.

   The main difficulty in defining this tactic is to understand how to
   construct the input expected by apply_in. *)
let package i = Goal.enter begin fun gl ->
  Tactics.apply_in true false i
   [(* this means that the applied theorem is not to be cleared. *)
    None, (CAst.make (c_M (),
           (* we don't specialize the theorem with extra values. *)
           Tactypes.NoBindings))]
     (* we don't destruct the result according to any intro_pattern *)
    None
  end

(* This function is meant to observe a type of shape (f a)
   and return the value a.  *)

(* Remark by Maxime: look for destApp combinator. *)
let unpack_type sigma term =
  let report () =
    CErrors.user_err (Pp.str "expecting a packed type") in
  match EConstr.kind sigma term with
  | Constr.App (_, [| ty |]) -> ty
  | _ -> report ()

(* This function is meant to observe a type of shape
   A -> pack B -> C and return A, B, C
  but it is not used in the current version of our tactic.
  It is kept as an example. *)
let two_lambda_pattern sigma term =
  let report () =
    CErrors.user_err (Pp.str "expecting two nested implications") in
(* Note that pattern-matching is always done through the EConstr.kind function,
   which only provides one-level deep patterns. *)
  match EConstr.kind sigma term with
  (* Here we recognize the outer implication *)
  | Constr.Prod (_, ty1, l1) ->
      (* Here we recognize the inner implication *)
      (match EConstr.kind sigma l1 with
      | Constr.Prod (n2, packed_ty2, deep_conclusion) ->
        (* Here we recognized that the second type is an application *)
        ty1, unpack_type sigma packed_ty2, deep_conclusion
      | _ -> report ())
  | _ -> report ()

(* In the environment of the goal, we can get the type of an assumption
  directly by a lookup.  The other solution is to call a low-cost retyping
  function like *)
let get_type_of_hyp env id =
  match EConstr.lookup_named id env with
  | Context.Named.Declaration.LocalAssum (_, ty) -> ty
  | _ -> CErrors.user_err (let open Pp in
                             str (Names.Id.to_string id) ++
                             str " is not a plain hypothesis")

let repackage i h_hyps_id = Goal.enter begin fun gl ->
    let env = Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let concl = Tacmach.New.pf_concl gl in
    let (ty1 : EConstr.t) = get_type_of_hyp env i in
    let (packed_ty2 : EConstr.t) = get_type_of_hyp env h_hyps_id in
    let ty2 = unpack_type sigma packed_ty2 in
    let new_packed_type = EConstr.mkApp (c_P (), [| ty1; ty2 |]) in
    let open EConstr in
    let new_packed_value =
        mkApp (c_R (), [| ty1; ty2; mkVar i;
          mkApp (c_U (), [| ty2; mkVar h_hyps_id|]) |]) in
    Refine.refine ~typecheck:true begin fun sigma ->
      let sigma, new_goal = Evarutil.new_evar env sigma
          (mkArrowR (mkApp(c_H (), [| new_packed_type |]))
             (Vars.lift 1 concl))
      in
      sigma, mkApp (new_goal,
                  [|mkApp(c_M (), [|new_packed_type; new_packed_value |]) |])
      end
    end

let pack_tactic i =
  let h_hyps_id = (Names.Id.of_string "packed_hyps") in
  Proofview.Goal.enter begin fun gl ->
    let hyps = Environ.named_context_val (Proofview.Goal.env gl) in
    if not (Termops.mem_named_context_val i hyps) then
      (CErrors.user_err
          (Pp.str ("no hypothesis named" ^ (Names.Id.to_string i))))
    else
      if Termops.mem_named_context_val h_hyps_id hyps then
          tclTHEN (repackage i h_hyps_id)
            (tclTHEN (Tactics.clear [h_hyps_id; i])
               (Tactics.introduction h_hyps_id))
      else
        tclTHEN (package i)
          (tclTHEN (Tactics.rename_hyp [i, h_hyps_id])
             (Tactics.move_hyp h_hyps_id Logic.MoveLast))
    end
