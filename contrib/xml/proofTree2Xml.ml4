let prooftreedtdname = "http://localhost:8081/getdtd?url=prooftree.dtd";;

let print_proof_tree curi pf proof_tree_to_constr constr_to_ids =
 let module PT = Proof_type in
 let module L = Logic in
 let module X = Xml in
  let ids_of_node node =
(*
   Acic.CicHash.find constr_to_ids (Hashtbl.find proof_tree_to_constr node)
*)
Acic.CicHash.find constr_to_ids (
try
   Hashtbl.find proof_tree_to_constr node
with e -> Pp.ppnl (Pp.(++) (Pp.str "NON TROVATO: ") (Refiner.print_proof Evd.empty Sign.empty_named_context node)) ; assert false)
  in
Pp.ppnl (Pp.str "BUG QUI: qualcuno ha fatto unsharing?") ;
  let rec aux node =
   let id = ids_of_node node in
    match node with
       {PT.ref=Some(PT.Prim _,nodes)} ->
         X.xml_nempty "Prim" ["of",id]
          [< (List.fold_left (fun i n -> [< i ; (aux n) >]) [<>] nodes) >]
	  
     | {PT.ref=Some(PT.Tactic (_,hidden_proof),nodes)} ->
         X.xml_nempty "Tactic" ["of",id]
          [< (List.fold_left (fun i n -> [< i ; (aux n) >]) [<>] nodes) >]
	  
     | {PT.ref=Some(PT.Change_evars,nodes)} ->
         X.xml_nempty "Change_evars" ["of",id]
          [< (List.fold_left (fun i n -> [< i ; (aux n) >]) [<>] nodes) >]
	  
     | {PT.ref=None;PT.goal=goal} ->
         X.xml_empty "Open_goal" ["of",id]
   in
    [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
       X.xml_cdata ("<!DOCTYPE ProofTree SYSTEM \"" ^ prooftreedtdname ^"\">\n\n");
       X.xml_nempty "ProofTree" ["of",curi] (aux pf)
    >]
;;
