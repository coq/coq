open Pp
open Glob_term
open Errors
open Util
open Names
open Decl_kinds
open Misctypes

(*
   Some basic functions to rebuild glob_constr
   In each of them the location is Loc.ghost
*)
let mkGRef ref = GRef(Loc.ghost,ref,None)
let mkGVar id = GVar(Loc.ghost,id)
let mkGApp(rt,rtl) = GApp(Loc.ghost,rt,rtl)
let mkGLambda(n,t,b) = GLambda(Loc.ghost,n,Explicit,t,b)
let mkGProd(n,t,b) = GProd(Loc.ghost,n,Explicit,t,b)
let mkGLetIn(n,t,b) = GLetIn(Loc.ghost,n,t,b)
let mkGCases(rto,l,brl) = GCases(Loc.ghost,Term.RegularStyle,rto,l,brl)
let mkGSort s = GSort(Loc.ghost,s)
let mkGHole () = GHole(Loc.ghost,Evar_kinds.BinderType Anonymous,Misctypes.IntroAnonymous,None)
let mkGCast(b,t) = GCast(Loc.ghost,b,CastConv t)

(*
  Some basic functions to decompose glob_constrs
  These are analogous to the ones constrs
*)
let glob_decompose_prod =
  let rec glob_decompose_prod args = function
  | GProd(_,n,k,t,b) ->
      glob_decompose_prod ((n,t)::args) b
  | rt -> args,rt
  in
  glob_decompose_prod []

let glob_decompose_prod_or_letin =
  let rec glob_decompose_prod args = function
  | GProd(_,n,k,t,b) ->
      glob_decompose_prod ((n,None,Some t)::args) b
  | GLetIn(_,n,t,b) ->
      glob_decompose_prod ((n,Some t,None)::args) b
  | rt -> args,rt
  in
  glob_decompose_prod []

let glob_compose_prod =
  List.fold_left (fun b (n,t) -> mkGProd(n,t,b))

let glob_compose_prod_or_letin =
  List.fold_left (
      fun concl decl ->
	match decl with
	  | (n,None,Some t) -> mkGProd(n,t,concl)
	  | (n,Some bdy,None) -> mkGLetIn(n,bdy,concl)
	  | _ -> assert false)

let glob_decompose_prod_n n =
  let rec glob_decompose_prod i args c =
    if i<=0 then args,c
    else
      match c with
	| GProd(_,n,_,t,b) ->
	    glob_decompose_prod (i-1) ((n,t)::args) b
	| rt -> args,rt
  in
  glob_decompose_prod n []


let glob_decompose_prod_or_letin_n n =
  let rec glob_decompose_prod i args c =
    if i<=0 then args,c
    else
      match c with
	| GProd(_,n,_,t,b) ->
	    glob_decompose_prod (i-1) ((n,None,Some t)::args) b
	| GLetIn(_,n,t,b) ->
	    glob_decompose_prod (i-1) ((n,Some t,None)::args) b
	| rt -> args,rt
  in
  glob_decompose_prod n []


let glob_decompose_app =
  let rec decompose_rapp acc rt =
(*     msgnl (str "glob_decompose_app on : "++ Printer.pr_glob_constr rt); *)
    match rt with
    | GApp(_,rt,rtl) ->
	decompose_rapp (List.fold_left (fun y x -> x::y) acc rtl) rt
    | rt -> rt,List.rev acc
  in
  decompose_rapp []




(* [glob_make_eq t1 t2] build the glob_constr corresponding to [t2 = t1] *)
let glob_make_eq ?(typ= mkGHole ()) t1 t2  =
  mkGApp(mkGRef (Lazy.force Coqlib.coq_eq_ref),[typ;t2;t1])

(* [glob_make_neq t1 t2] build the glob_constr corresponding to [t1 <> t2] *)
let glob_make_neq t1 t2 =
  mkGApp(mkGRef (Lazy.force Coqlib.coq_not_ref),[glob_make_eq t1 t2])

(* [glob_make_or P1 P2] build the glob_constr corresponding to [P1 \/ P2] *)
let glob_make_or t1 t2 = mkGApp (mkGRef(Lazy.force Coqlib.coq_or_ref),[t1;t2])

(* [glob_make_or_list [P1;...;Pn]] build the glob_constr corresponding
   to [P1 \/ ( .... \/ Pn)]
*)
let rec glob_make_or_list = function
  | [] -> invalid_arg "mk_or"
  | [e] -> e
  | e::l -> glob_make_or e (glob_make_or_list l)


let remove_name_from_mapping mapping na =
  match na with
    | Anonymous -> mapping
    | Name id -> Id.Map.remove id mapping

let change_vars =
  let rec change_vars mapping rt =
    match rt with
      | GRef _ -> rt
      | GVar(loc,id) ->
	  let new_id =
	    try
	      Id.Map.find id mapping
	    with Not_found -> id
	  in
	  GVar(loc,new_id)
      | GEvar _ -> rt
      | GPatVar _ -> rt
      | GApp(loc,rt',rtl) ->
	  GApp(loc,
	       change_vars mapping rt',
	       List.map (change_vars mapping) rtl
	      )
      | GLambda(loc,name,k,t,b) ->
	  GLambda(loc,
		  name,
		  k,
		  change_vars mapping t,
		  change_vars (remove_name_from_mapping mapping name) b
		 )
      | GProd(loc,name,k,t,b) ->
	  GProd(loc,
		  name,
	          k,
		  change_vars mapping t,
		  change_vars (remove_name_from_mapping mapping name) b
		 )
      | GLetIn(loc,name,def,b) ->
	  GLetIn(loc,
		 name,
		 change_vars mapping def,
		 change_vars (remove_name_from_mapping mapping name) b
		)
      | GLetTuple(loc,nal,(na,rto),b,e) ->
	  let new_mapping = List.fold_left remove_name_from_mapping mapping nal in
	  GLetTuple(loc,
		    nal,
		    (na, Option.map (change_vars mapping) rto),
		    change_vars mapping b,
		    change_vars new_mapping e
		   )
      | GCases(loc,sty,infos,el,brl) ->
	  GCases(loc,sty,
		 infos,
		 List.map (fun (e,x) -> (change_vars mapping e,x)) el,
		 List.map (change_vars_br mapping) brl
		)
      | GIf(loc,b,(na,e_option),lhs,rhs) ->
	  GIf(loc,
	      change_vars mapping b,
	      (na,Option.map (change_vars mapping) e_option),
	      change_vars mapping lhs,
	      change_vars mapping rhs
	     )
      | GRec _ -> error "Local (co)fixes are not supported"
      | GSort _ -> rt
      | GHole _ -> rt
      | GCast(loc,b,c) ->
	  GCast(loc,change_vars mapping b,
		Miscops.map_cast_type (change_vars mapping) c)
  and change_vars_br mapping ((loc,idl,patl,res) as br) =
    let new_mapping = List.fold_right Id.Map.remove idl mapping in
    if Id.Map.is_empty new_mapping
    then br
    else (loc,idl,patl,change_vars new_mapping res)
  in
  change_vars



let rec alpha_pat excluded pat =
  match pat with
    | PatVar(loc,Anonymous) ->
	let new_id = Indfun_common.fresh_id excluded "_x" in
	PatVar(loc,Name new_id),(new_id::excluded),Id.Map.empty
    | PatVar(loc,Name id) ->
	if Id.List.mem id excluded
	then
	  let new_id = Namegen.next_ident_away id excluded in
	  PatVar(loc,Name new_id),(new_id::excluded),
	(Id.Map.add id new_id Id.Map.empty)
	else pat,excluded,Id.Map.empty
    | PatCstr(loc,constr,patl,na) ->
	let new_na,new_excluded,map =
	  match na with
	    | Name id when Id.List.mem id excluded ->
		let new_id = Namegen.next_ident_away id excluded in
		Name new_id,new_id::excluded, Id.Map.add id new_id Id.Map.empty
	    | _ -> na,excluded,Id.Map.empty
	in
	let new_patl,new_excluded,new_map =
	  List.fold_left
	    (fun (patl,excluded,map) pat ->
	       let new_pat,new_excluded,new_map = alpha_pat excluded pat in
	       (new_pat::patl,new_excluded,Id.Map.fold Id.Map.add new_map map)
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
	 new_pat::patl,new_excluded,(Id.Map.fold Id.Map.add new_map map)
      )
      ([],excluded,Id.Map.empty)
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
      | GRef _ | GVar _ | GEvar _ | GPatVar _ -> rt
      | GLambda(loc,Anonymous,k,t,b) ->
	  let new_id = Namegen.next_ident_away (Id.of_string "_x") excluded in
	  let new_excluded = new_id :: excluded in
	  let new_t = alpha_rt new_excluded t in
	  let new_b = alpha_rt new_excluded b in
	  GLambda(loc,Name new_id,k,new_t,new_b)
      | GProd(loc,Anonymous,k,t,b) ->
	let new_t = alpha_rt excluded t in
	let new_b = alpha_rt excluded b in
	GProd(loc,Anonymous,k,new_t,new_b)
    | GLetIn(loc,Anonymous,t,b) ->
	let new_t = alpha_rt excluded t in
	let new_b = alpha_rt excluded b in
	GLetIn(loc,Anonymous,new_t,new_b)
    | GLambda(loc,Name id,k,t,b) ->
	let new_id = Namegen.next_ident_away id excluded in
	let t,b =
	  if Id.equal new_id id
	  then t,b
	  else
	    let replace = change_vars (Id.Map.add id new_id Id.Map.empty) in
	    (t,replace b)
	in
	let new_excluded = new_id::excluded in
	let new_t = alpha_rt new_excluded t in
	let new_b = alpha_rt new_excluded b in
	GLambda(loc,Name new_id,k,new_t,new_b)
    | GProd(loc,Name id,k,t,b) ->
	let new_id = Namegen.next_ident_away id excluded in
	let new_excluded = new_id::excluded in
	let t,b =
	  if Id.equal new_id id
	  then t,b
	  else
	    let replace = change_vars (Id.Map.add id new_id Id.Map.empty) in
	    (t,replace b)
	in
	let new_t = alpha_rt new_excluded t in
	let new_b = alpha_rt new_excluded b in
	GProd(loc,Name new_id,k,new_t,new_b)
    | GLetIn(loc,Name id,t,b) ->
	let new_id = Namegen.next_ident_away id excluded in
	let t,b =
	  if Id.equal new_id id
	  then t,b
	  else
	    let replace = change_vars (Id.Map.add id new_id Id.Map.empty) in
	    (t,replace b)
	in
	let new_excluded = new_id::excluded in
	let new_t = alpha_rt new_excluded t in
	let new_b = alpha_rt new_excluded b in
	GLetIn(loc,Name new_id,new_t,new_b)


    | GLetTuple(loc,nal,(na,rto),t,b) ->
	let rev_new_nal,new_excluded,mapping =
	  List.fold_left
	    (fun (nal,excluded,mapping) na ->
	       match na with
		 | Anonymous -> (na::nal,excluded,mapping)
		 | Name id ->
		     let new_id = Namegen.next_ident_away id excluded in
		     if Id.equal new_id id
		     then
		       na::nal,id::excluded,mapping
		     else
		       (Name new_id)::nal,id::excluded,(Id.Map.add id new_id mapping)
	    )
	    ([],excluded,Id.Map.empty)
	    nal
	in
	let new_nal = List.rev rev_new_nal in
	let new_rto,new_t,new_b =
	  if Id.Map.is_empty mapping
	  then rto,t,b
	  else let replace = change_vars mapping in
	  (Option.map replace rto, t,replace b)
	in
	let new_t = alpha_rt new_excluded new_t in
	let new_b = alpha_rt new_excluded new_b in
	let new_rto = Option.map (alpha_rt new_excluded) new_rto  in
	GLetTuple(loc,new_nal,(na,new_rto),new_t,new_b)
    | GCases(loc,sty,infos,el,brl) ->
	let new_el =
	  List.map (function (rt,i) -> alpha_rt excluded rt, i) el
	in
	GCases(loc,sty,infos,new_el,List.map (alpha_br excluded) brl)
    | GIf(loc,b,(na,e_o),lhs,rhs) ->
	GIf(loc,alpha_rt excluded b,
	    (na,Option.map (alpha_rt excluded) e_o),
	    alpha_rt excluded lhs,
	    alpha_rt excluded rhs
	   )
    | GRec _ -> error "Not handled GRec"
    | GSort _ -> rt
    | GHole _ -> rt
    | GCast (loc,b,c) ->
	GCast(loc,alpha_rt excluded b,
	      Miscops.map_cast_type (alpha_rt excluded) c)
    | GApp(loc,f,args) ->
	GApp(loc,
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
    | GRef _ ->  false
    | GVar(_,id') -> Id.compare id' id == 0
    | GEvar _ -> false
    | GPatVar _ -> false
    | GApp(_,rt,rtl) -> List.exists is_free_in (rt::rtl)
    | GLambda(_,n,_,t,b) | GProd(_,n,_,t,b) | GLetIn(_,n,t,b) ->
	let check_in_b =
	  match n with
	    | Name id' -> not (Id.equal id' id)
	    | _ -> true
	in
	is_free_in t || (check_in_b && is_free_in b)
    | GCases(_,_,_,el,brl) ->
	(List.exists (fun (e,_) -> is_free_in e) el) ||
	  List.exists is_free_in_br brl
    | GLetTuple(_,nal,_,b,t) ->
	let check_in_nal =
	  not (List.exists (function Name id' -> Id.equal id' id | _ -> false) nal)
	in
	is_free_in t  || (check_in_nal && is_free_in b)

    | GIf(_,cond,_,br1,br2) ->
	is_free_in cond || is_free_in br1 || is_free_in br2
    | GRec _ -> raise (UserError("",str "Not handled GRec"))
    | GSort _ -> false
    | GHole _ -> false
    | GCast (_,b,(CastConv t|CastVM t|CastNative t)) -> is_free_in b || is_free_in t
    | GCast (_,b,CastCoerce) -> is_free_in b
  and is_free_in_br (_,ids,_,rt) =
    (not (Id.List.mem id ids)) && is_free_in rt
  in
  is_free_in



let rec pattern_to_term  = function
  | PatVar(loc,Anonymous) -> assert false
  | PatVar(loc,Name id) ->
	mkGVar id
  | PatCstr(loc,constr,patternl,_) ->
      let cst_narg =
	Inductiveops.constructor_nallargs_env
	  (Global.env ())
	  constr
      in
      let implicit_args =
	Array.to_list
	  (Array.init
	     (cst_narg - List.length patternl)
	     (fun _ -> mkGHole ())
	  )
      in
      let patl_as_term =
	List.map pattern_to_term patternl
      in
      mkGApp(mkGRef(Globnames.ConstructRef constr),
	     implicit_args@patl_as_term
	    )



let replace_var_by_term x_id term =
  let rec replace_var_by_pattern rt =
    match rt with
      | GRef _ -> rt
      | GVar(_,id) when Id.compare id x_id == 0 -> term
      | GVar _ -> rt
      | GEvar _ -> rt
      | GPatVar _ -> rt
      | GApp(loc,rt',rtl) ->
	  GApp(loc,
	       replace_var_by_pattern rt',
	       List.map replace_var_by_pattern rtl
	      )
      | GLambda(_,Name id,_,_,_) when Id.compare id x_id == 0 -> rt
      | GLambda(loc,name,k,t,b) ->
	  GLambda(loc,
		  name,
		  k,
		  replace_var_by_pattern t,
		  replace_var_by_pattern b
		 )
      | GProd(_,Name id,_,_,_) when Id.compare id x_id == 0 -> rt
      | GProd(loc,name,k,t,b) ->
	  GProd(loc,
		  name,
	          k,
		  replace_var_by_pattern t,
		  replace_var_by_pattern b
		 )
      | GLetIn(_,Name id,_,_) when Id.compare id x_id == 0 -> rt
      | GLetIn(loc,name,def,b) ->
	  GLetIn(loc,
		 name,
		 replace_var_by_pattern def,
		 replace_var_by_pattern b
		)
      | GLetTuple(_,nal,_,_,_)
	  when List.exists (function Name id -> Id.equal id x_id | _ -> false) nal  ->
	  rt
      | GLetTuple(loc,nal,(na,rto),def,b) ->
	  GLetTuple(loc,
		    nal,
		    (na,Option.map replace_var_by_pattern rto),
		    replace_var_by_pattern def,
		    replace_var_by_pattern b
		   )
      | GCases(loc,sty,infos,el,brl) ->
	  GCases(loc,sty,
		 infos,
		 List.map (fun (e,x) -> (replace_var_by_pattern e,x)) el,
		 List.map replace_var_by_pattern_br brl
		)
      | GIf(loc,b,(na,e_option),lhs,rhs) ->
	  GIf(loc, replace_var_by_pattern b,
	      (na,Option.map replace_var_by_pattern e_option),
	      replace_var_by_pattern lhs,
	      replace_var_by_pattern rhs
	     )
      | GRec _ -> raise (UserError("",str "Not handled GRec"))
      | GSort _ -> rt
      | GHole _ -> rt
      | GCast(loc,b,c) ->
	  GCast(loc,replace_var_by_pattern b,
		Miscops.map_cast_type replace_var_by_pattern c)
  and replace_var_by_pattern_br ((loc,idl,patl,res) as br) =
    if List.exists (fun id -> Id.compare id x_id == 0) idl
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
	     if not (eq_constructor constructor2 constructor1)
	     then raise NotUnifiable
	     else
	       let eqs' =
		 try (List.combine cpl1 cpl2) @ eqs
		 with Invalid_argument _ -> anomaly (Pp.str "are_unifiable_aux")
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
	     if not (eq_constructor constructor2 constructor1)
	     then raise NotUnifiable
	     else
	       let eqs' =
		 try (List.combine cpl1 cpl2) @ eqs
		 with Invalid_argument _ -> anomaly (Pp.str "eq_cases_pattern_aux")
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
    | PatVar(_,Name id) -> Id.Set.add id ids
    | PatCstr(_,_,patl,_) -> List.fold_left ids_of_pat ids patl
  in
  ids_of_pat Id.Set.empty

let id_of_name = function
  | Names.Anonymous -> Id.of_string "x"
  | Names.Name x -> x

(* TODO: finish Rec caes *)
let ids_of_glob_constr c =
  let rec ids_of_glob_constr acc c =
    let idof = id_of_name in
    match c with
      | GVar (_,id) -> id::acc
      | GApp (loc,g,args) ->
          ids_of_glob_constr [] g @ List.flatten (List.map (ids_of_glob_constr []) args) @ acc
      | GLambda (loc,na,k,ty,c) -> idof na :: ids_of_glob_constr [] ty @ ids_of_glob_constr [] c @ acc
      | GProd (loc,na,k,ty,c) -> idof na :: ids_of_glob_constr [] ty @ ids_of_glob_constr [] c @ acc
      | GLetIn (loc,na,b,c) -> idof na :: ids_of_glob_constr [] b @ ids_of_glob_constr [] c @ acc
      | GCast (loc,c,(CastConv t|CastVM t|CastNative t)) -> ids_of_glob_constr [] c @ ids_of_glob_constr [] t @ acc
      | GCast (loc,c,CastCoerce) -> ids_of_glob_constr [] c @ acc
      | GIf (loc,c,(na,po),b1,b2) -> ids_of_glob_constr [] c @ ids_of_glob_constr [] b1 @ ids_of_glob_constr [] b2 @ acc
      | GLetTuple (_,nal,(na,po),b,c) ->
          List.map idof nal @ ids_of_glob_constr [] b @ ids_of_glob_constr [] c @ acc
      | GCases (loc,sty,rtntypopt,tml,brchl) ->
	  List.flatten (List.map (fun (_,idl,patl,c) -> idl @ ids_of_glob_constr [] c) brchl)
      | GRec _ -> failwith "Fix inside a constructor branch"
      | (GSort _ | GHole _ | GRef _ | GEvar _ | GPatVar _) -> []
  in
  (* build the set *)
  List.fold_left (fun acc x -> Id.Set.add x acc) Id.Set.empty (ids_of_glob_constr [] c)





let zeta_normalize =
  let rec zeta_normalize_term rt =
    match rt with
      | GRef _ -> rt
      | GVar _ -> rt
      | GEvar _ -> rt
      | GPatVar _ -> rt
      | GApp(loc,rt',rtl) ->
	  GApp(loc,
	       zeta_normalize_term rt',
	       List.map zeta_normalize_term rtl
	      )
      | GLambda(loc,name,k,t,b) ->
	  GLambda(loc,
		  name,
		  k,
		  zeta_normalize_term t,
		  zeta_normalize_term b
		 )
      | GProd(loc,name,k,t,b) ->
	  GProd(loc,
		name,
	        k,
		zeta_normalize_term t,
		zeta_normalize_term b
		 )
      | GLetIn(_,Name id,def,b) ->
	  zeta_normalize_term (replace_var_by_term id def b)
      | GLetIn(loc,Anonymous,def,b) -> zeta_normalize_term b
      | GLetTuple(loc,nal,(na,rto),def,b) ->
	  GLetTuple(loc,
		    nal,
		    (na,Option.map zeta_normalize_term rto),
		    zeta_normalize_term def,
		    zeta_normalize_term b
		   )
      | GCases(loc,sty,infos,el,brl) ->
	  GCases(loc,sty,
		 infos,
		 List.map (fun (e,x) -> (zeta_normalize_term e,x)) el,
		 List.map zeta_normalize_br brl
		)
      | GIf(loc,b,(na,e_option),lhs,rhs) ->
	  GIf(loc, zeta_normalize_term b,
	      (na,Option.map zeta_normalize_term e_option),
	      zeta_normalize_term lhs,
	      zeta_normalize_term rhs
	     )
      | GRec _ -> raise (UserError("",str "Not handled GRec"))
      | GSort _ -> rt
      | GHole _ -> rt
      | GCast(loc,b,c) ->
	  GCast(loc,zeta_normalize_term b,
                Miscops.map_cast_type zeta_normalize_term c)
  and zeta_normalize_br (loc,idl,patl,res) =
    (loc,idl,patl,zeta_normalize_term res)
  in
  zeta_normalize_term




let expand_as =

  let rec add_as map pat =
    match pat with
      | PatVar _ -> map
      | PatCstr(_,_,patl,Name id) ->
	  Id.Map.add id (pattern_to_term pat) (List.fold_left add_as map patl)
      | PatCstr(_,_,patl,_) -> List.fold_left add_as map patl
  in
  let rec expand_as map rt =
    match rt with
      | GRef _ | GEvar _ | GPatVar _ | GSort _ | GHole _ -> rt
      | GVar(_,id) ->
	  begin
	    try
	      Id.Map.find id map
	    with Not_found -> rt
	  end
      | GApp(loc,f,args) -> GApp(loc,expand_as map f,List.map (expand_as map) args)
      | GLambda(loc,na,k,t,b) -> GLambda(loc,na,k,expand_as map t, expand_as map b)
      | GProd(loc,na,k,t,b) -> GProd(loc,na,k,expand_as map t, expand_as map b)
      | GLetIn(loc,na,v,b) -> GLetIn(loc,na, expand_as map v,expand_as map b)
      | GLetTuple(loc,nal,(na,po),v,b) ->
	  GLetTuple(loc,nal,(na,Option.map (expand_as map) po),
		    expand_as map v, expand_as map b)
      | GIf(loc,e,(na,po),br1,br2) ->
	  GIf(loc,expand_as map e,(na,Option.map (expand_as map) po),
	      expand_as map br1, expand_as map br2)
      | GRec _ ->  error "Not handled GRec"
      | GCast(loc,b,c) ->
	  GCast(loc,expand_as map b,
		Miscops.map_cast_type (expand_as map) c)
      | GCases(loc,sty,po,el,brl) ->
	  GCases(loc, sty, Option.map (expand_as map) po, List.map (fun (rt,t) -> expand_as map rt,t) el,
		List.map (expand_as_br map) brl)
  and expand_as_br map (loc,idl,cpl,rt) =
    (loc,idl,cpl, expand_as (List.fold_left add_as map cpl) rt)
  in
  expand_as Id.Map.empty
