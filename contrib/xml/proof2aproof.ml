(* Note: we can not use the Set module here because we _need_ physical *)
(* equality and there exists no comparison function compatible with    *)
(* physical equality.                                                  *)
module S =
 struct
  let empty = []
  let mem = List.memq
  let add x l = x::l
 end
;;

(* evar reduction that preserves some terms *)
let nf_evar sigma ~preserve =
 let module T = Term in
  let rec aux t =
   if preserve t then t else
    match T.kind_of_term t with
     | T.Rel _ | T.Meta _ | T.Var _ | T.Sort _ | T.Const _ | T.Ind _
     | T.Construct _ -> t
     | T.Cast (c1,c2) -> T.mkCast (aux c1, aux c2)
     | T.Prod (na,c1,c2) -> T.mkProd (na, aux c1, aux c2)
     | T.Lambda (na,t,c) -> T.mkLambda (na, aux t, aux c)
     | T.LetIn (na,b,t,c) -> T.mkLetIn (na, aux b, aux t, aux c)
     | T.App (c,l) ->
        let c' = aux c in
        let l' = Array.map aux l in
         (match T.kind_of_term c' with
             T.App (c'',l'') -> T.mkApp (c'', Array.append l'' l')
           | T.Cast (he,_) ->
              (match T.kind_of_term he with
                  T.App (c'',l'') -> T.mkApp (c'', Array.append l'' l')
                | _ -> T.mkApp (c', l')
              )
           | _ -> T.mkApp (c', l'))
     | T.Evar (e,l) when Evd.in_dom sigma e & Evd.is_defined sigma e ->
	aux (Instantiate.existential_value sigma (e,l))
     | T.Evar (e,l) -> T.mkEvar (e, Array.map aux l)
     | T.Case (ci,p,c,bl) -> T.mkCase (ci, aux p, aux c, Array.map aux bl)
     | T.Fix (ln,(lna,tl,bl)) ->
         T.mkFix (ln,(lna,Array.map aux tl,Array.map aux bl))
     | T.CoFix(ln,(lna,tl,bl)) ->
         T.mkCoFix (ln,(lna,Array.map aux tl,Array.map aux bl))
   in
    aux
;;

let extract_open_proof sigma pf =
 let module PT = Proof_type in
 let module L = Logic in
  let sigma = ref sigma in
  let proof_tree_to_constr = Hashtbl.create 503 in
  let unshared_constrs = ref S.empty in
  let rec proof_extractor vl node =
   let constr =
    match node with
       {PT.ref=Some(PT.Prim _,_)} as pf ->
        L.prim_extractor proof_extractor vl pf
	  
     | {PT.ref=Some(PT.Tactic (_,hidden_proof),spfl)} ->
	 let sgl,v = Refiner.frontier hidden_proof in
	 let flat_proof = v spfl in
	 proof_extractor vl flat_proof
	  
     | {PT.ref=Some(PT.Change_evars,[pf])} -> (proof_extractor vl) pf
	  
     | {PT.ref=None;PT.goal=goal} ->
	 let visible_rels =
           Util.map_succeed
             (fun id ->
                (* Section variables are in the [id] list but are not *)
                (* lambda abstracted in the term [vl]                 *)
                try let n = Util.list_index id vl in (n,id)
	        with Not_found -> failwith "caught")
(*CSC: the above function must be modified such that when it is found  *)
(*CSC: it becomes a Rel; otherwise a Var. Then it can be already used  *)
(*CSC: as the evar_instance. Ordering the instance becomes useless (it *)
(*CSC: will already be ordered.                                        *)
             (Termops.ids_of_named_context goal.Evd.evar_hyps) in
	 let sorted_rels =
	   Sort.list (fun (n1,_) (n2,_) -> n1 < n2 ) visible_rels in
	 let context =
          List.map
            (fun (_,id) -> Sign.lookup_named id goal.Evd.evar_hyps)
            sorted_rels
         in
(*CSC: the section variables in the right order must be added too *)
         let evar_instance = List.map (fun (n,_) -> Term.mkRel n) sorted_rels in
         let env = Global.env_of_context context in
         let sigma',evar =
          Evarutil.new_isevar_sign env !sigma goal.Evd.evar_concl evar_instance
         in
         sigma := sigma' ;
         evar
	  
     | _ -> Util.anomaly "Bug : a case has been forgotten in proof_extractor"
   in
    let unsharedconstr =
     let evar_nf_constr =
      nf_evar !sigma ~preserve:(function e -> S.mem e !unshared_constrs) constr
     in
      Term.unshare
       ~already_unshared:(function e -> S.mem e !unshared_constrs)
       evar_nf_constr
    in
(*
Pp.ppnl (Pp.(++) (Pp.str "Registro tattica che ha creato:") (Printer.prterm unsharedconstr)) ;
*)
     Hashtbl.add proof_tree_to_constr node unsharedconstr ;
     unshared_constrs := S.add unsharedconstr !unshared_constrs ;
     unsharedconstr
  in
  let pfterm = proof_extractor [] pf in
  (pfterm, !sigma, proof_tree_to_constr)
;;

let extract_open_pftreestate pts =
  extract_open_proof (Refiner.evc_of_pftreestate pts)
   (Refiner.proof_of_pftreestate pts)
;;
