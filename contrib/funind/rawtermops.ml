open Pp 
open Rawterm
open Util
open Names
(* Ocaml 3.06 Map.S does not handle is_empty *)
let idmap_is_empty m = m = Idmap.empty

(* 
   Some basic functions to rebuild rawconstr
   In each of them the location is Util.dummy_loc
*)
let mkRRef ref = RRef(dummy_loc,ref)
let mkRVar id = RVar(dummy_loc,id)
let mkRApp(rt,rtl) = RApp(dummy_loc,rt,rtl)
let mkRLambda(n,t,b) = RLambda(dummy_loc,n,t,b)
let mkRProd(n,t,b) = RProd(dummy_loc,n,t,b)
let mkRLetIn(n,t,b) = RLetIn(dummy_loc,n,t,b)
let mkRCases(rto,l,brl) = RCases(dummy_loc,rto,l,brl)
let mkRSort s = RSort(dummy_loc,s)
let mkRHole () = RHole(dummy_loc,Evd.BinderType Anonymous)
let mkRCast(b,t) = RCast(dummy_loc,b,CastConv (Term.DEFAULTcast,t))

(*
  Some basic functions to decompose rawconstrs
  These are analogous to the ones constrs
*)
let raw_decompose_prod = 
  let rec raw_decompose_prod args = function 
  | RProd(_,n,t,b) -> 
      raw_decompose_prod ((n,t)::args) b 
  | rt -> args,rt
  in
  raw_decompose_prod []

let raw_decompose_prod_or_letin = 
  let rec raw_decompose_prod args = function 
  | RProd(_,n,t,b) -> 
      raw_decompose_prod ((n,None,Some t)::args) b 
  | RLetIn(_,n,t,b) -> 
      raw_decompose_prod ((n,Some t,None)::args) b 
  | rt -> args,rt
  in
  raw_decompose_prod []

let raw_compose_prod = 
  List.fold_left (fun b (n,t) -> mkRProd(n,t,b))

let raw_compose_prod_or_letin = 
  List.fold_left (
      fun concl decl -> 
	match decl with 
	  | (n,None,Some t) -> mkRProd(n,t,concl)
	  | (n,Some bdy,None) -> mkRLetIn(n,bdy,concl)
	  | _ -> assert false)

let raw_decompose_prod_n n = 
  let rec raw_decompose_prod i args c = 
    if i<=0 then args,c
    else
      match c with
	| RProd(_,n,t,b) -> 
	    raw_decompose_prod (i-1) ((n,t)::args) b 
	| rt -> args,rt
  in
  raw_decompose_prod n []


let raw_decompose_prod_or_letin_n n = 
  let rec raw_decompose_prod i args c = 
    if i<=0 then args,c
    else
      match c with
	| RProd(_,n,t,b) -> 
	    raw_decompose_prod (i-1) ((n,None,Some t)::args) b 
	| RLetIn(_,n,t,b) -> 
	    raw_decompose_prod (i-1) ((n,Some t,None)::args) b 
	| rt -> args,rt
  in
  raw_decompose_prod n []


let raw_decompose_app = 
  let rec decompose_rapp acc rt =
(*     msgnl (str "raw_decompose_app on : "++ Printer.pr_rawconstr rt); *)
    match rt with 
    | RApp(_,rt,rtl) -> 
	decompose_rapp (List.fold_left (fun y x -> x::y) acc rtl) rt
    | rt -> rt,List.rev acc
  in
  decompose_rapp [] 




(* [raw_make_eq t1 t2] build the rawconstr corresponding to [t2 = t1] *) 
let raw_make_eq ?(typ= mkRHole ()) t1 t2  = 
  mkRApp(mkRRef (Lazy.force Coqlib.coq_eq_ref),[typ;t2;t1])

(* [raw_make_neq t1 t2] build the rawconstr corresponding to [t1 <> t2] *) 
let raw_make_neq t1 t2 = 
  mkRApp(mkRRef (Lazy.force Coqlib.coq_not_ref),[raw_make_eq t1 t2])

(* [raw_make_or P1 P2] build the rawconstr corresponding to [P1 \/ P2] *) 
let raw_make_or t1 t2 = mkRApp (mkRRef(Lazy.force Coqlib.coq_or_ref),[t1;t2])

(* [raw_make_or_list [P1;...;Pn]] build the rawconstr corresponding 
   to [P1 \/ ( .... \/ Pn)] 
*) 
let rec raw_make_or_list = function  
  | [] -> raise (Invalid_argument "mk_or")
  | [e] -> e
  | e::l -> raw_make_or e (raw_make_or_list l)

  
let remove_name_from_mapping mapping na = 
  match na with 
    | Anonymous -> mapping 
    | Name id -> Idmap.remove id mapping

let change_vars = 
  let rec change_vars mapping rt = 
    match rt with 
      | RRef _ -> rt 
      | RVar(loc,id) ->  
	  let new_id = 
	    try 
	      Idmap.find id mapping 
	    with Not_found -> id 
	  in
	  RVar(loc,new_id)
      | REvar _ -> rt 
      | RPatVar _ -> rt 
      | RApp(loc,rt',rtl) -> 
	  RApp(loc,
	       change_vars mapping rt',
	       List.map (change_vars mapping) rtl
	      )
      | RLambda(loc,name,t,b) -> 
	  RLambda(loc,
		  name,
		  change_vars mapping t,
		  change_vars (remove_name_from_mapping mapping name) b
		 )
      | RProd(loc,name,t,b) -> 
	  RProd(loc,
		  name,
		  change_vars mapping t,
		  change_vars (remove_name_from_mapping mapping name) b
		 )
      | RLetIn(loc,name,def,b) -> 
	  RLetIn(loc,
		 name,
		 change_vars mapping def,
		 change_vars (remove_name_from_mapping mapping name) b
		)
      | RLetTuple(loc,nal,(na,rto),b,e) -> 
	  let new_mapping = List.fold_left remove_name_from_mapping mapping nal in 
	  RLetTuple(loc,
		    nal,
		    (na, Option.map (change_vars mapping) rto), 
		    change_vars mapping b, 
		    change_vars new_mapping e
		   )
      | RCases(loc,infos,el,brl) -> 
	  RCases(loc,
		 infos,
		 List.map (fun (e,x) -> (change_vars mapping e,x)) el, 
		 List.map (change_vars_br mapping) brl
		)
      | RIf(loc,b,(na,e_option),lhs,rhs) -> 
	  RIf(loc,
	      change_vars mapping b,
	      (na,Option.map (change_vars mapping) e_option),
	      change_vars mapping lhs,
	      change_vars mapping rhs
	     )
      | RRec _ -> error "Local (co)fixes are not supported"
      | RSort _ -> rt 
      | RHole _ -> rt 
      | RCast(loc,b,CastConv (k,t)) -> 
	  RCast(loc,change_vars mapping b, CastConv (k,change_vars mapping t))
      | RCast(loc,b,CastCoerce) -> 
	  RCast(loc,change_vars mapping b,CastCoerce)
      | RDynamic _ -> error "Not handled RDynamic"
  and change_vars_br mapping ((loc,idl,patl,res) as br) = 
    let new_mapping = List.fold_right Idmap.remove idl mapping in 
    if idmap_is_empty new_mapping 
    then br 
    else (loc,idl,patl,change_vars new_mapping res)
  in
  change_vars 



let rec alpha_pat excluded pat = 
  match pat with 
    | PatVar(loc,Anonymous) -> 
	let new_id = Indfun_common.fresh_id excluded "_x" in 
	PatVar(loc,Name new_id),(new_id::excluded),Idmap.empty
    | PatVar(loc,Name id) -> 
	if List.mem id excluded 
	then 
	  let new_id = Nameops.next_ident_away id excluded in 
	  PatVar(loc,Name new_id),(new_id::excluded),
	(Idmap.add id new_id Idmap.empty)
	else pat,excluded,Idmap.empty
    | PatCstr(loc,constr,patl,na) -> 
	let new_na,new_excluded,map = 
	  match na with 
	    | Name id when List.mem id excluded -> 
		let new_id = Nameops.next_ident_away id excluded in 
		Name new_id,new_id::excluded, Idmap.add id new_id Idmap.empty
	    | _ -> na,excluded,Idmap.empty
	in 
	let new_patl,new_excluded,new_map = 
	  List.fold_left 
	    (fun (patl,excluded,map) pat -> 
	       let new_pat,new_excluded,new_map = alpha_pat excluded pat in 
	       (new_pat::patl,new_excluded,Idmap.fold Idmap.add new_map map)
	    )
	    ([],new_excluded,map)
	    patl
	in 
	PatCstr(loc,constr,List.rev new_patl,new_na),new_excluded,new_map

let alpha_patl excluded patl  = 
  let patl,new_excluded,map = 
    List.fold_left 
      (fun (patl,excluded,map) pat -> 
	 let new_pat,new_excluded,new_map = alpha_pat excluded pat in 
	 new_pat::patl,new_excluded,(Idmap.fold Idmap.add new_map map)
      )
      ([],excluded,Idmap.empty)
      patl
  in 
  (List.rev patl,new_excluded,map)



  
let raw_get_pattern_id pat acc = 
  let rec get_pattern_id pat = 
    match pat with 
      | PatVar(loc,Anonymous) -> assert false
      | PatVar(loc,Name id) -> 
	  [id]
      | PatCstr(loc,constr,patternl,_) -> 
	  List.fold_right 
	  (fun pat idl -> 
	     let idl' = get_pattern_id pat in 
	     idl'@idl
	  )
	    patternl 
	    []
  in
  (get_pattern_id pat)@acc

let get_pattern_id pat = raw_get_pattern_id pat []
	      
let rec alpha_rt excluded rt = 
  let new_rt = 
    match rt with   
      | RRef _ | RVar _ | REvar _ | RPatVar _ -> rt
      | RLambda(loc,Anonymous,t,b) -> 
	  let new_id = Nameops.next_ident_away (id_of_string "_x") excluded in 
	  let new_excluded = new_id :: excluded in 
	  let new_t = alpha_rt new_excluded t in 
	  let new_b = alpha_rt new_excluded b in 
	  RLambda(loc,Name new_id,new_t,new_b)
      | RProd(loc,Anonymous,t,b) -> 
	let new_t = alpha_rt excluded t in 
	let new_b = alpha_rt excluded b in 
	RProd(loc,Anonymous,new_t,new_b)
    | RLetIn(loc,Anonymous,t,b) -> 
	let new_t = alpha_rt excluded t in 
	let new_b = alpha_rt excluded b in 
	RLetIn(loc,Anonymous,new_t,new_b)
    | RLambda(loc,Name id,t,b) -> 
	let new_id = Nameops.next_ident_away id excluded in 
	let t,b = 
	  if new_id = id 
	  then t,b
	  else 
	    let replace = change_vars (Idmap.add id new_id Idmap.empty) in 
	    (t,replace b)
	in
	let new_excluded = new_id::excluded in 
	let new_t = alpha_rt new_excluded t in 
	let new_b = alpha_rt new_excluded b in 
	RLambda(loc,Name new_id,new_t,new_b)
    | RProd(loc,Name id,t,b) -> 
	let new_id = Nameops.next_ident_away id excluded in 
	let new_excluded = new_id::excluded in 
	let t,b = 
	  if new_id = id 
	  then t,b
	  else 
	    let replace = change_vars (Idmap.add id new_id Idmap.empty) in 
	    (t,replace b)
	in
	let new_t = alpha_rt new_excluded t in 
	let new_b = alpha_rt new_excluded b in 
	RProd(loc,Name new_id,new_t,new_b)
    | RLetIn(loc,Name id,t,b) -> 
	let new_id = Nameops.next_ident_away id excluded in 
	let t,b = 
	  if new_id = id 
	  then t,b
	  else 
	    let replace = change_vars (Idmap.add id new_id Idmap.empty) in 
	    (t,replace b)
	in
	let new_excluded = new_id::excluded in 
	let new_t = alpha_rt new_excluded t in 
	let new_b = alpha_rt new_excluded b in 
	RLetIn(loc,Name new_id,new_t,new_b)


    | RLetTuple(loc,nal,(na,rto),t,b) -> 
	let rev_new_nal,new_excluded,mapping = 
	  List.fold_left 
	    (fun (nal,excluded,mapping) na -> 
	       match na with 
		 | Anonymous -> (na::nal,excluded,mapping)
		 | Name id ->  
		     let new_id = Nameops.next_ident_away id excluded in 
		     if new_id = id 
		     then 
		       na::nal,id::excluded,mapping 
		     else 
		       (Name new_id)::nal,id::excluded,(Idmap.add id new_id mapping)
	    )
	    ([],excluded,Idmap.empty)
	    nal
	in
	let new_nal = List.rev rev_new_nal in 
	let new_rto,new_t,new_b = 
	  if idmap_is_empty mapping
	  then rto,t,b
	  else let replace = change_vars mapping in 
	  (Option.map replace rto, t,replace b)
	in
	let new_t = alpha_rt new_excluded new_t in 
	let new_b = alpha_rt new_excluded new_b in 
	let new_rto = Option.map (alpha_rt new_excluded) new_rto  in
	RLetTuple(loc,new_nal,(na,new_rto),new_t,new_b)
    | RCases(loc,infos,el,brl) -> 
	let new_el = 
	  List.map (function (rt,i) -> alpha_rt excluded rt, i) el 
	in 
	RCases(loc,infos,new_el,List.map (alpha_br excluded) brl) 
    | RIf(loc,b,(na,e_o),lhs,rhs) -> 
	RIf(loc,alpha_rt excluded b,
	    (na,Option.map (alpha_rt excluded) e_o),
	    alpha_rt excluded lhs,
	    alpha_rt excluded rhs
	   )
    | RRec _ -> error "Not handled RRec"
    | RSort _ -> rt 
    | RHole _ -> rt 
    | RCast (loc,b,CastConv (k,t)) -> 
	RCast(loc,alpha_rt excluded b,CastConv(k,alpha_rt excluded t))
    | RCast (loc,b,CastCoerce) -> 
	RCast(loc,alpha_rt excluded b,CastCoerce)
    | RDynamic _ -> error "Not handled RDynamic"
    | RApp(loc,f,args) -> 
	RApp(loc,
	     alpha_rt excluded f,
	     List.map (alpha_rt excluded) args
	    )
  in 
  new_rt

and alpha_br excluded (loc,ids,patl,res) = 
  let new_patl,new_excluded,mapping = alpha_patl excluded patl in 
  let new_ids = List.fold_right raw_get_pattern_id new_patl [] in 
  let new_excluded = new_ids@excluded in 
  let renamed_res = change_vars mapping res in 
  let new_res = alpha_rt new_excluded renamed_res in 
  (loc,new_ids,new_patl,new_res)
    
(* 
   [is_free_in id rt] checks if [id] is a free variable in [rt]
*)
let is_free_in id =
  let rec is_free_in = function
    | RRef _ ->  false
    | RVar(_,id') -> id_ord id' id == 0
    | REvar _ -> false
    | RPatVar _ -> false
    | RApp(_,rt,rtl) -> List.exists is_free_in (rt::rtl)
    | RLambda(_,n,t,b) | RProd(_,n,t,b) | RLetIn(_,n,t,b) ->
	let check_in_b =
	  match n with
	    | Name id' -> id_ord id' id <> 0
	    | _ -> true
	in
	is_free_in t || (check_in_b && is_free_in b)
    | RCases(_,_,el,brl) ->
	(List.exists (fun (e,_) -> is_free_in e) el) ||
	  List.exists is_free_in_br brl

    | RLetTuple(_,nal,_,b,t) -> 
	let check_in_nal = 
	  not (List.exists (function Name id' -> id'= id | _ -> false) nal) 
	in 
	is_free_in t  || (check_in_nal && is_free_in b)
	  
    | RIf(_,cond,_,br1,br2) ->
	is_free_in cond || is_free_in br1 || is_free_in br2
    | RRec _ -> raise (UserError("",str "Not handled RRec"))
    | RSort _ -> false
    | RHole _ -> false
    | RCast (_,b,CastConv (_,t)) -> is_free_in b || is_free_in t
    | RCast (_,b,CastCoerce) -> is_free_in b
    | RDynamic _ -> raise (UserError("",str "Not handled RDynamic"))
  and is_free_in_br (_,ids,_,rt) =
    (not (List.mem id ids)) && is_free_in rt
  in
  is_free_in
      


let rec pattern_to_term  = function
  | PatVar(loc,Anonymous) -> assert false
  | PatVar(loc,Name id) ->
	mkRVar id
  | PatCstr(loc,constr,patternl,_) ->
      let cst_narg =
	Inductiveops.mis_constructor_nargs_env
	  (Global.env ())
	  constr
      in
      let implicit_args =
	Array.to_list
	  (Array.init
	     (cst_narg - List.length patternl)
	     (fun _ -> mkRHole ())
	  )
      in
      let patl_as_term =
	List.map pattern_to_term patternl
      in
      mkRApp(mkRRef(Libnames.ConstructRef constr),
	     implicit_args@patl_as_term
	    )

  

let replace_var_by_term x_id term = 
  let rec replace_var_by_pattern rt = 
    match rt with 
      | RRef _ -> rt 
      | RVar(_,id) when id_ord id x_id == 0 -> term
      | RVar _ -> rt 
      | REvar _ -> rt 
      | RPatVar _ -> rt 
      | RApp(loc,rt',rtl) -> 
	  RApp(loc,
	       replace_var_by_pattern rt',
	       List.map replace_var_by_pattern rtl
	      )
      | RLambda(_,Name id,_,_) when id_ord id x_id == 0 -> rt
      | RLambda(loc,name,t,b) -> 
	  RLambda(loc,
		  name,
		  replace_var_by_pattern t,
		  replace_var_by_pattern b
		 )
      | RProd(_,Name id,_,_) when id_ord id x_id == 0 -> rt
      | RProd(loc,name,t,b) -> 
	  RProd(loc,
		  name,
		  replace_var_by_pattern t,
		  replace_var_by_pattern b
		 )
      | RLetIn(_,Name id,_,_) when id_ord id x_id == 0 -> rt
      | RLetIn(loc,name,def,b) -> 
	  RLetIn(loc,
		 name,
		 replace_var_by_pattern def,
		 replace_var_by_pattern b
		)
      | RLetTuple(_,nal,_,_,_) 
	  when List.exists (function Name id -> id = x_id | _ -> false) nal  ->  
	  rt
      | RLetTuple(loc,nal,(na,rto),def,b) -> 
	  RLetTuple(loc,
		    nal,
		    (na,Option.map replace_var_by_pattern rto),
		    replace_var_by_pattern def,
		    replace_var_by_pattern b
		   )
      | RCases(loc,infos,el,brl) -> 
	  RCases(loc,
		 infos,
		 List.map (fun (e,x) -> (replace_var_by_pattern e,x)) el, 
		 List.map replace_var_by_pattern_br brl
		)
      | RIf(loc,b,(na,e_option),lhs,rhs) -> 
	  RIf(loc, replace_var_by_pattern b,
	      (na,Option.map replace_var_by_pattern e_option),
	      replace_var_by_pattern lhs,
	      replace_var_by_pattern rhs
	     )
      | RRec _ -> raise (UserError("",str "Not handled RRec"))
      | RSort _ -> rt 
      | RHole _ -> rt 
      | RCast(loc,b,CastConv(k,t)) -> 
	  RCast(loc,replace_var_by_pattern b,CastConv(k,replace_var_by_pattern t))
      | RCast(loc,b,CastCoerce) -> 
	  RCast(loc,replace_var_by_pattern b,CastCoerce)
      | RDynamic _ -> raise (UserError("",str "Not handled RDynamic"))
  and replace_var_by_pattern_br ((loc,idl,patl,res) as br) = 
    if List.exists (fun id -> id_ord id x_id == 0) idl 
    then br 
    else (loc,idl,patl,replace_var_by_pattern res)
  in
  replace_var_by_pattern 




(* checking unifiability of patterns *) 
exception NotUnifiable  

let rec are_unifiable_aux  = function 
  | [] -> () 
  | eq::eqs -> 
      match eq with 
	 | PatVar _,_ | _,PatVar _ -> are_unifiable_aux eqs 
	 | PatCstr(_,constructor1,cpl1,_),PatCstr(_,constructor2,cpl2,_) -> 
	     if constructor2 <> constructor1 
	     then raise NotUnifiable
	     else 
	       let eqs' = 
 		 try  ((List.combine cpl1 cpl2)@eqs)
		 with _ -> anomaly "are_unifiable_aux" 
	       in
	       are_unifiable_aux eqs'
		 
let are_unifiable pat1 pat2 = 
  try 
    are_unifiable_aux [pat1,pat2];
    true
  with NotUnifiable -> false


let rec eq_cases_pattern_aux  = function 
  | [] -> () 
  | eq::eqs -> 
      match eq with 
	 | PatVar _,PatVar _ -> eq_cases_pattern_aux eqs 
	 | PatCstr(_,constructor1,cpl1,_),PatCstr(_,constructor2,cpl2,_) -> 
	     if constructor2 <> constructor1 
	     then raise NotUnifiable
	     else 
	       let eqs' = 
 		 try  ((List.combine cpl1 cpl2)@eqs)
		 with _ -> anomaly "eq_cases_pattern_aux" 
	       in
	       eq_cases_pattern_aux eqs'
	 | _ -> raise NotUnifiable

let eq_cases_pattern pat1 pat2 = 
  try
    eq_cases_pattern_aux [pat1,pat2];
    true
  with NotUnifiable -> false



let ids_of_pat = 
  let rec ids_of_pat ids = function 
    | PatVar(_,Anonymous) -> ids 
    | PatVar(_,Name id) -> Idset.add id ids 
    | PatCstr(_,_,patl,_) -> List.fold_left ids_of_pat ids patl
  in
  ids_of_pat Idset.empty 
  
let id_of_name = function 
  | Names.Anonymous -> id_of_string "x" 
  | Names.Name x -> x

(* TODO: finish Rec caes *)
let ids_of_rawterm c = 
  let rec ids_of_rawterm acc c = 
    let idof = id_of_name in
    match c with
      | RVar (_,id) -> id::acc
      | RApp (loc,g,args) -> 
          ids_of_rawterm [] g @ List.flatten (List.map (ids_of_rawterm []) args) @ acc
      | RLambda (loc,na,ty,c) -> idof na :: ids_of_rawterm [] ty @ ids_of_rawterm [] c @ acc
      | RProd (loc,na,ty,c) -> idof na :: ids_of_rawterm [] ty @ ids_of_rawterm [] c @ acc
      | RLetIn (loc,na,b,c) -> idof na :: ids_of_rawterm [] b @ ids_of_rawterm [] c @ acc
      | RCast (loc,c,CastConv(k,t)) -> ids_of_rawterm [] c @ ids_of_rawterm [] t @ acc
      | RCast (loc,c,CastCoerce) -> ids_of_rawterm [] c @ acc
      | RIf (loc,c,(na,po),b1,b2) -> ids_of_rawterm [] c @ ids_of_rawterm [] b1 @ ids_of_rawterm [] b2 @ acc
      | RLetTuple (_,nal,(na,po),b,c) -> 
          List.map idof nal @ ids_of_rawterm [] b @ ids_of_rawterm [] c @ acc
      | RCases (loc,rtntypopt,tml,brchl) -> 
	  List.flatten (List.map (fun (_,idl,patl,c) -> idl @ ids_of_rawterm [] c) brchl)
      | RRec _ -> failwith "Fix inside a constructor branch"
      | (RSort _ | RHole _ | RRef _ | REvar _ | RPatVar _ | RDynamic _) -> []
  in
  (* build the set *)
  List.fold_left (fun acc x -> Idset.add x acc) Idset.empty (ids_of_rawterm [] c)
  




let zeta_normalize = 
  let rec zeta_normalize_term rt = 
    match rt with 
      | RRef _ -> rt 
      | RVar _ -> rt 
      | REvar _ -> rt 
      | RPatVar _ -> rt 
      | RApp(loc,rt',rtl) -> 
	  RApp(loc,
	       zeta_normalize_term rt',
	       List.map zeta_normalize_term rtl
	      )
      | RLambda(loc,name,t,b) -> 
	  RLambda(loc,
		  name,
		  zeta_normalize_term t,
		  zeta_normalize_term b
		 )
      | RProd(loc,name,t,b) -> 
	  RProd(loc,
		name, 		  
		zeta_normalize_term t,
		zeta_normalize_term b
		 )
      | RLetIn(_,Name id,def,b) -> 
	  zeta_normalize_term (replace_var_by_term id def b)
      | RLetIn(loc,Anonymous,def,b) -> zeta_normalize_term b
      | RLetTuple(loc,nal,(na,rto),def,b) -> 
	  RLetTuple(loc,
		    nal,
		    (na,Option.map zeta_normalize_term rto),
		    zeta_normalize_term def,
		    zeta_normalize_term b
		   )
      | RCases(loc,infos,el,brl) -> 
	  RCases(loc,
		 infos,
		 List.map (fun (e,x) -> (zeta_normalize_term e,x)) el, 
		 List.map zeta_normalize_br brl
		)
      | RIf(loc,b,(na,e_option),lhs,rhs) -> 
	  RIf(loc, zeta_normalize_term b,
	      (na,Option.map zeta_normalize_term e_option),
	      zeta_normalize_term lhs,
	      zeta_normalize_term rhs
	     )
      | RRec _ -> raise (UserError("",str "Not handled RRec"))
      | RSort _ -> rt 
      | RHole _ -> rt 
      | RCast(loc,b,CastConv(k,t)) -> 
	  RCast(loc,zeta_normalize_term b,CastConv(k,zeta_normalize_term t))
      | RCast(loc,b,CastCoerce) -> 
	  RCast(loc,zeta_normalize_term b,CastCoerce)
      | RDynamic _ -> raise (UserError("",str "Not handled RDynamic"))
  and zeta_normalize_br (loc,idl,patl,res) = 
    (loc,idl,patl,zeta_normalize_term res)
  in
  zeta_normalize_term 




let expand_as = 
  
  let rec add_as map pat = 
    match pat with 
      | PatVar _ -> map 
      | PatCstr(_,_,patl,Name id) -> 
	  Idmap.add id (pattern_to_term pat) (List.fold_left add_as map patl)
      | PatCstr(_,_,patl,_) -> List.fold_left add_as map patl
  in 
  let rec expand_as map rt = 
    match rt with 
      | RRef _ | REvar _ | RPatVar _ | RSort _ | RHole _ -> rt 
      | RVar(_,id) -> 
	  begin
	    try 
	      Idmap.find id map
	    with Not_found -> rt 
	  end
      | RApp(loc,f,args) -> RApp(loc,expand_as map f,List.map (expand_as map) args)
      | RLambda(loc,na,t,b) -> RLambda(loc,na,expand_as map t, expand_as map b)
      | RProd(loc,na,t,b) -> RProd(loc,na,expand_as map t, expand_as map b)
      | RLetIn(loc,na,v,b) -> RLetIn(loc,na, expand_as map v,expand_as map b)
      | RLetTuple(loc,nal,(na,po),v,b) ->
	  RLetTuple(loc,nal,(na,Option.map (expand_as map) po),
		    expand_as map v, expand_as map b)
      | RIf(loc,e,(na,po),br1,br2) ->
	  RIf(loc,expand_as map e,(na,Option.map (expand_as map) po),
	      expand_as map br1, expand_as map br2)
      | RRec _ ->  error "Not handled RRec"
      | RDynamic _ -> error "Not handled RDynamic"
      | RCast(loc,b,CastConv(kind,t)) -> RCast(loc,expand_as map b,CastConv(kind,expand_as map t))
      | RCast(loc,b,CastCoerce) -> RCast(loc,expand_as map b,CastCoerce)
      | RCases(loc,po,el,brl) ->
	  RCases(loc, Option.map (expand_as map) po, List.map (fun (rt,t) -> expand_as map rt,t) el,
		List.map (expand_as_br map) brl)
	    
  and expand_as_br map (loc,idl,cpl,rt) = 
    (loc,idl,cpl,    expand_as (List.fold_left add_as map cpl) rt)
  in
  expand_as Idmap.empty 
