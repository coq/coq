open Proofview

let constants = ref ([] : EConstr.t list)

let collect_constants () =
  if (!constants = []) then
    let open Coqlib in
    let open EConstr in
    let open Universes in
    let gr_H = find_reference "Tuto3" ["Tuto3"; "Data"] "hide" in
    let gr_M = find_reference "Tuto3" ["Tuto3"; "Data"] "hide_marker" in
    constants := List.map (fun x -> of_constr (constr_of_global x))
      [gr_H; gr_M];
    !constants
  else
    !constants

let c_H () =
  match collect_constants () with
    it :: _ -> it
  | _ -> failwith "could not obtain an internal representation of hide"

let c_M () =
  match collect_constants () with
    _ :: it :: _ -> it
  | _ -> failwith "could not obtain an internal representation of hide_marker"

let package i = Goal.enter begin fun gl ->
  Tactics.apply_in true false i
   [None, (CAst.make (c_M (), Misctypes.NoBindings))] None
  end
(*
let package i = Goal.enter begin fun gl ->
    let h_hyps_id = (Names.Id.of_string "hidden_hyps") in
    let env = Goal.env gl in
    let store = Goal.extra gl in
    let concl = Tacmach.New.pf_concl in
    
    let ty_i = ... in
    let ev = Evarutil.new_evar in
    mkApp (mkLambda(h_hyps_id, mkApp(c_h, [|ty_i|] , ev),
           [| mkApp (c_hm, [| ty_ev; EConstr.mkVar i |]) |])
end
 *)

let repackage _ = failwith "todo"

let hide_tactic i =
  let h_hyps_id = (Names.Id.of_string "hidden_hyps") in
  Proofview.Goal.enter begin fun gl ->
    let hyps = Environ.named_context_val (Proofview.Goal.env gl) in
    if not (Termops.mem_named_context_val i hyps) then
      (CErrors.user_err
          (Pp.str ("no hypothesis named" ^ (Names.Id.to_string i))))
    else
      if Termops.mem_named_context_val h_hyps_id hyps then
          tclTHEN (Tactics.revert [i; h_hyps_id]) (repackage ())
      else
        package i
    end
      
      
