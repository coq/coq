(**************************************************************************
  *********                  ntrefiner.ml                          *********
  **************************************************************************)

(*
open Std;;
open Names;;
open Generic;;
open Term;;
open Termenv;;
open More_util;;
open Proof_trees;;
open Logic;;
open Refiner;;
open Evd;;


(*the only difference with extract_open_proof is that the 
  path of the unsolved goal in put in metavar assoc list 
  extract_open_proof : constr signature -> proof
  -> constr * (int * constr) list
  takes a constr signature corresponding to global definitions
  and a (not necessarly complete) proof
  and gives a pair (pfterm,obl)
  where pfterm is the constr corresponding to the proof
  and obl is an int*constr list [ (m1,c1) ; ... ; (mn,cn)]
  where the mi are metavariables numbers, and ci are their types.
  Their proof should be completed in order to complete the initial proof*)
let nt_extract_open_proof sign pf =
 let open_obligations = ref [] in
 let st = Stack.create () in
 Stack.push 1 st;
 let rec proof_extractor vl =
  function
     | {ref=Some ((PRIM _), _)} as pf -> prim_extractor proof_extractor vl pf
     | {ref=Some ((TACTIC (str, _)), spfl); subproof=Some hidden_proof} ->
      let sgl, v = frontier hidden_proof in
      let flat_proof = v spfl in
      if str = "Interpret" then (Stack.push 1 st);
       let c = proof_extractor vl flat_proof in
       if str = "Interpret" then
        (Stack.pop st; Stack.push ((Stack.pop st) + 1) st); c
     | {ref=Some ((CONTEXT ctxt), (pf :: []))} -> (proof_extractor vl) pf
     | {ref=Some ((LOCAL_CONSTRAINTS lc), (pf :: []))} ->
      (proof_extractor vl) pf
     | {ref=None; goal=goal} ->
      let visible_rels = map_succeed (function id ->
       (match lookup_id id vl with
       | GLOBNAME _ -> failwith "caught"
       | RELNAME (n, _) -> n, id)) (ids_of_sign goal.hyps) in
      let
      sorted_rels = Sort.list (fun (n1, _) (n2, _) -> n1>n2) visible_rels
      in
      let
      abs_concl =
       List.fold_right
       (fun (_, id) concl -> mkNamedProd id (snd (lookup_sign id goal.hyps)) concl)
       sorted_rels goal.concl in
      let path =
       let l = ref [] in
       let f i = l:=i::!l in
       Stack.iter f st; List.tl !l in
      Stack.push ((Stack.pop st) + 1) st;
       let mv = newMETA () in
       open_obligations:=(mv, (abs_concl, path))::!open_obligations;
       applist (DOP0 (Meta mv), List.map (function n, _ -> Rel n) sorted_rels)
     | _ -> error "ntrfiner__nt_extract_open_proof" in
 let pfterm = proof_extractor (gLOB sign) pf in
 pfterm, List.rev !open_obligations;;

*)
