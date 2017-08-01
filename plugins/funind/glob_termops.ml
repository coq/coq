open Pp
open Glob_term
open CErrors
open Util
open Names
open Decl_kinds
open Misctypes

(*
   Some basic functions to rebuild glob_constr
   In each of them the location is Loc.ghost
*)
let mkGRef ref          = CAst.make @@ GRef(ref,None)
let mkGVar id           = CAst.make @@ GVar(id)
let mkGApp(rt,rtl)      = CAst.make @@ GApp(rt,rtl)
let mkGLambda(n,t,b)    = CAst.make @@ GLambda(n,Explicit,t,b)
let mkGProd(n,t,b)      = CAst.make @@ GProd(n,Explicit,t,b)
let mkGLetIn(n,b,t,c)   = CAst.make @@ GLetIn(n,b,t,c)
let mkGCases(rto,l,brl) = CAst.make @@ GCases(Term.RegularStyle,rto,l,brl)
let mkGSort s           = CAst.make @@ GSort(s)
let mkGHole ()          = CAst.make @@ GHole(Evar_kinds.BinderType Anonymous,Misctypes.IntroAnonymous,None)
let mkGCast(b,t)        = CAst.make @@ GCast(b,CastConv t)

(*
  Some basic functions to decompose glob_constrs
  These are analogous to the ones constrs
*)
let glob_decompose_prod =
  let rec glob_decompose_prod args = function
  | { CAst.v = GProd(n,k,t,b) } ->
      glob_decompose_prod ((n,t)::args) b
  | rt -> args,rt
  in
  glob_decompose_prod []

let glob_decompose_prod_or_letin =
  let rec glob_decompose_prod args = function
  | { CAst.v = GProd(n,k,t,b) } ->
      glob_decompose_prod ((n,None,Some t)::args) b
  | { CAst.v = GLetIn(n,b,t,c) } ->
      glob_decompose_prod ((n,Some b,t)::args) c
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
	  | (n,Some bdy,t) -> mkGLetIn(n,bdy,t,concl)
	  | _ -> assert false)

let glob_decompose_prod_n n =
  let rec glob_decompose_prod i args c =
    if i<=0 then args,c
    else
      match c with
	| { CAst.v = GProd(n,_,t,b) } ->
	    glob_decompose_prod (i-1) ((n,t)::args) b
	| rt -> args,rt
  in
  glob_decompose_prod n []


let glob_decompose_prod_or_letin_n n =
  let rec glob_decompose_prod i args c =
    if i<=0 then args,c
    else
      match c with
	| { CAst.v = GProd(n,_,t,b) } ->
	    glob_decompose_prod (i-1) ((n,None,Some t)::args) b
	| { CAst.v = GLetIn(n,b,t,c) } ->
	    glob_decompose_prod (i-1) ((n,Some b,t)::args) c
	| rt -> args,rt
  in
  glob_decompose_prod n []


let glob_decompose_app =
  let rec decompose_rapp acc rt =
(*     msgnl (str "glob_decompose_app on : "++ Printer.pr_glob_constr rt); *)
    match rt with
    | { CAst.v = GApp(rt,rtl) } ->
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
    CAst.map_with_loc (fun ?loc -> function
      | GRef _ as x -> x
      | GVar id ->
	  let new_id =
	    try
	      Id.Map.find id mapping
	    with Not_found -> id
	  in
	  GVar(new_id)
      | GEvar _ as x   -> x
      | GPatVar _ as x -> x
      | GApp(rt',rtl) ->
	  GApp(change_vars mapping rt',
	       List.map (change_vars mapping) rtl
	      )
      | GLambda(name,k,t,b) ->
	  GLambda(name,
		  k,
		  change_vars mapping t,
		  change_vars (remove_name_from_mapping mapping name) b
		 )
      | GProd(name,k,t,b) ->
	  GProd(  name,
	          k,
		  change_vars mapping t,
		  change_vars (remove_name_from_mapping mapping name) b
		 )
      | GLetIn(name,def,typ,b) ->
	  GLetIn(name,
		 change_vars mapping def,
		 Option.map (change_vars mapping) typ,
		 change_vars (remove_name_from_mapping mapping name) b
		)
      | GLetTuple(nal,(na,rto),b,e) ->
	  let new_mapping = List.fold_left remove_name_from_mapping mapping nal in
	  GLetTuple(nal,
		    (na, Option.map (change_vars mapping) rto),
		    change_vars mapping b,
		    change_vars new_mapping e
		   )
      | GCases(sty,infos,el,brl) ->
	  GCases(sty,
		 infos,
		 List.map (fun (e,x) -> (change_vars mapping e,x)) el,
		 List.map (change_vars_br mapping) brl
		)
      | GIf(b,(na,e_option),lhs,rhs) ->
	  GIf(change_vars mapping b,
	      (na,Option.map (change_vars mapping) e_option),
	      change_vars mapping lhs,
	      change_vars mapping rhs
	     )
      | GRec _ -> user_err ?loc Pp.(str "Local (co)fixes are not supported")
      | GSort _ as x -> x
      | GHole _ as x -> x
      | GCast(b,c) ->
	  GCast(change_vars mapping b,
		Miscops.map_cast_type (change_vars mapping) c)
      ) rt
  and change_vars_br mapping ((loc,(idl,patl,res)) as br) =
    let new_mapping = List.fold_right Id.Map.remove idl mapping in
    if Id.Map.is_empty new_mapping
    then br
    else (loc,(idl,patl,change_vars new_mapping res))
  in
  change_vars



let rec alpha_pat excluded pat =
  let loc = pat.CAst.loc in
  match pat.CAst.v with
    | PatVar Anonymous ->
	let new_id = Indfun_common.fresh_id excluded "_x" in
	(CAst.make ?loc @@ PatVar(Name new_id)),(new_id::excluded),Id.Map.empty
    | PatVar(Name id) ->
	if Id.List.mem id excluded
	then
	  let new_id = Namegen.next_ident_away id excluded in
	  (CAst.make ?loc @@ PatVar(Name new_id)),(new_id::excluded),
	(Id.Map.add id new_id Id.Map.empty)
	else pat, excluded,Id.Map.empty
    | PatCstr(constr,patl,na) ->
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
        (CAst.make ?loc @@ PatCstr(constr,List.rev new_patl,new_na)),new_excluded,new_map

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
    match pat.CAst.v with
      | PatVar(Anonymous) -> assert false
      | PatVar(Name id) ->
	  [id]
      | PatCstr(constr,patternl,_) ->
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
  let loc = rt.CAst.loc in
  let new_rt = CAst.make ?loc @@
    match rt.CAst.v with
      | GRef _ | GVar _ | GEvar _ | GPatVar _ as rt -> rt
      | GLambda(Anonymous,k,t,b) ->
	  let new_id = Namegen.next_ident_away (Id.of_string "_x") excluded in
	  let new_excluded = new_id :: excluded in
	  let new_t = alpha_rt new_excluded t in
	  let new_b = alpha_rt new_excluded b in
	  GLambda(Name new_id,k,new_t,new_b)
      | GProd(Anonymous,k,t,b) ->
	let new_t = alpha_rt excluded t in
	let new_b = alpha_rt excluded b in
	GProd(Anonymous,k,new_t,new_b)
    | GLetIn(Anonymous,b,t,c) ->
	let new_b = alpha_rt excluded b in
	let new_t = Option.map (alpha_rt excluded) t in
	let new_c = alpha_rt excluded c in
	GLetIn(Anonymous,new_b,new_t,new_c)
    | GLambda(Name id,k,t,b) ->
	let new_id = Namegen.next_ident_away id excluded in
	let t,b =
	  if Id.equal new_id id
	  then t, b
	  else
	    let replace = change_vars (Id.Map.add id new_id Id.Map.empty) in
	    (t,replace b)
	in
	let new_excluded = new_id::excluded in
	let new_t = alpha_rt new_excluded t in
	let new_b = alpha_rt new_excluded b in
	GLambda(Name new_id,k,new_t,new_b)
    | GProd(Name id,k,t,b) ->
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
	GProd(Name new_id,k,new_t,new_b)
    | GLetIn(Name id,b,t,c) ->
	let new_id = Namegen.next_ident_away id excluded in
	let c =
	  if Id.equal new_id id then c
	  else change_vars (Id.Map.add id new_id Id.Map.empty) c
	in
	let new_excluded = new_id::excluded in
	let new_b = alpha_rt new_excluded b in
	let new_t = Option.map (alpha_rt new_excluded) t in
	let new_c = alpha_rt new_excluded c in
	GLetIn(Name new_id,new_b,new_t,new_c)

    | GLetTuple(nal,(na,rto),t,b) ->
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
	GLetTuple(new_nal,(na,new_rto),new_t,new_b)
    | GCases(sty,infos,el,brl) ->
	let new_el =
	  List.map (function (rt,i) -> alpha_rt excluded rt, i) el
	in
	GCases(sty,infos,new_el,List.map (alpha_br excluded) brl)
    | GIf(b,(na,e_o),lhs,rhs) ->
	GIf(alpha_rt excluded b,
	    (na,Option.map (alpha_rt excluded) e_o),
	    alpha_rt excluded lhs,
	    alpha_rt excluded rhs
	   )
    | GRec _ -> user_err Pp.(str "Not handled GRec")
    | GSort _
    | GHole _ as rt -> rt
    | GCast (b,c) ->
	GCast(alpha_rt excluded b,
	      Miscops.map_cast_type (alpha_rt excluded) c)
    | GApp(f,args) ->
	GApp(alpha_rt excluded f,
	     List.map (alpha_rt excluded) args
	    )
  in
  new_rt

and alpha_br excluded (loc,(ids,patl,res)) =
  let new_patl,new_excluded,mapping = alpha_patl excluded patl in
  let new_ids = List.fold_right raw_get_pattern_id new_patl [] in
  let new_excluded = new_ids@excluded in
  let renamed_res = change_vars mapping res in
  let new_res = alpha_rt new_excluded renamed_res in
  (loc,(new_ids,new_patl,new_res))

(*
   [is_free_in id rt] checks if [id] is a free variable in [rt]
*)
let is_free_in id =
  let rec is_free_in x = CAst.with_loc_val (fun ?loc -> function
    | GRef _ ->  false
    | GVar id' -> Id.compare id' id == 0
    | GEvar _ -> false
    | GPatVar _ -> false
    | GApp(rt,rtl) -> List.exists is_free_in (rt::rtl)
    | GLambda(n,_,t,b) | GProd(n,_,t,b) ->
	let check_in_b =
	  match n with
	    | Name id' -> not (Id.equal id' id)
	    | _ -> true
	in
	is_free_in t || (check_in_b && is_free_in b)
    | GLetIn(n,b,t,c) ->
	let check_in_c =
	  match n with
	    | Name id' -> not (Id.equal id' id)
	    | _ -> true
	in
	is_free_in b || Option.cata is_free_in true t || (check_in_c && is_free_in c)
    | GCases(_,_,el,brl) ->
	(List.exists (fun (e,_) -> is_free_in e) el) ||
	  List.exists is_free_in_br brl
    | GLetTuple(nal,_,b,t) ->
	let check_in_nal =
	  not (List.exists (function Name id' -> Id.equal id' id | _ -> false) nal)
	in
	is_free_in t  || (check_in_nal && is_free_in b)

    | GIf(cond,_,br1,br2) ->
	is_free_in cond || is_free_in br1 || is_free_in br2
    | GRec _  -> user_err Pp.(str "Not handled GRec")
    | GSort _ -> false
    | GHole _ -> false
    | GCast (b,(CastConv t|CastVM t|CastNative t)) -> is_free_in b || is_free_in t
    | GCast (b,CastCoerce) -> is_free_in b
    ) x
  and is_free_in_br (_,(ids,_,rt)) =
    (not (Id.List.mem id ids)) && is_free_in rt
  in
  is_free_in



let rec pattern_to_term pt = CAst.with_val (function
  | PatVar Anonymous -> assert false
  | PatVar(Name id) ->
	mkGVar id
  | PatCstr(constr,patternl,_) ->
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
  ) pt


let replace_var_by_term x_id term =
  let rec replace_var_by_pattern x = CAst.map (function
      | GVar id when Id.compare id x_id == 0 -> term.CAst.v
      | GRef _
      | GVar _
      | GEvar _
      | GPatVar _ as rt -> rt
      | GApp(rt',rtl) ->
	  GApp(replace_var_by_pattern rt',
	       List.map replace_var_by_pattern rtl
	      )
      | GLambda(Name id,_,_,_) as rt when Id.compare id x_id == 0 -> rt
      | GLambda(name,k,t,b) ->
	  GLambda(name,
		  k,
		  replace_var_by_pattern t,
		  replace_var_by_pattern b
		 )
      | GProd(Name id,_,_,_) as rt when Id.compare id x_id == 0 -> rt
      | GProd(name,k,t,b) ->
	  GProd(  name,
	          k,
		  replace_var_by_pattern t,
		  replace_var_by_pattern b
		 )
      | GLetIn(Name id,_,_,_) as rt when Id.compare id x_id == 0 -> rt
      | GLetIn(name,def,typ,b) ->
	  GLetIn(name,
		 replace_var_by_pattern def,
		 Option.map (replace_var_by_pattern) typ,
		 replace_var_by_pattern b
		)
      | GLetTuple(nal,_,_,_) as rt
	  when List.exists (function Name id -> Id.equal id x_id | _ -> false) nal  ->
	  rt
      | GLetTuple(nal,(na,rto),def,b) ->
	  GLetTuple(nal,
		    (na,Option.map replace_var_by_pattern rto),
		    replace_var_by_pattern def,
		    replace_var_by_pattern b
		   )
      | GCases(sty,infos,el,brl) ->
	  GCases(sty,
		 infos,
		 List.map (fun (e,x) -> (replace_var_by_pattern e,x)) el,
		 List.map replace_var_by_pattern_br brl
		)
      | GIf(b,(na,e_option),lhs,rhs) ->
	  GIf(replace_var_by_pattern b,
	      (na,Option.map replace_var_by_pattern e_option),
	      replace_var_by_pattern lhs,
	      replace_var_by_pattern rhs
	     )
      | GRec _ -> raise (UserError(None,str "Not handled GRec"))
      | GSort _
      | GHole _ as rt -> rt
      | GCast(b,c) ->
	  GCast(replace_var_by_pattern b,
		Miscops.map_cast_type replace_var_by_pattern c)
    ) x
  and replace_var_by_pattern_br ((loc,(idl,patl,res)) as br) =
    if List.exists (fun id -> Id.compare id x_id == 0) idl
    then br
    else (loc,(idl,patl,replace_var_by_pattern res))
  in
  replace_var_by_pattern




(* checking unifiability of patterns *)
exception NotUnifiable

let rec are_unifiable_aux  = function
  | [] -> ()
  | eq::eqs ->
      let open CAst in
      match eq with
	 | { v = PatVar _ },_ | _, { v = PatVar _ } -> are_unifiable_aux eqs
	 | { v = PatCstr(constructor1,cpl1,_) }, { v = PatCstr(constructor2,cpl2,_) } ->
	     if not (eq_constructor constructor2 constructor1)
	     then raise NotUnifiable
	     else
	       let eqs' =
		 try (List.combine cpl1 cpl2) @ eqs
		 with Invalid_argument _ -> anomaly (Pp.str "are_unifiable_aux.")
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
      let open CAst in
      match eq with
	 | { v = PatVar _ }, { v = PatVar _ } -> eq_cases_pattern_aux eqs
	 | { v = PatCstr(constructor1,cpl1,_) }, { v = PatCstr(constructor2,cpl2,_) } ->
	     if not (eq_constructor constructor2 constructor1)
	     then raise NotUnifiable
	     else
	       let eqs' =
		 try (List.combine cpl1 cpl2) @ eqs
		 with Invalid_argument _ -> anomaly (Pp.str "eq_cases_pattern_aux.")
	       in
	       eq_cases_pattern_aux eqs'
	 | _ -> raise NotUnifiable

let eq_cases_pattern pat1 pat2 =
  try
    eq_cases_pattern_aux [pat1,pat2];
    true
  with NotUnifiable -> false



let ids_of_pat =
  let rec ids_of_pat ids = CAst.with_val (function
    | PatVar Anonymous -> ids
    | PatVar(Name id) -> Id.Set.add id ids
    | PatCstr(_,patl,_) -> List.fold_left ids_of_pat ids patl
    )
  in
  ids_of_pat Id.Set.empty

let id_of_name = function
  | Anonymous -> Id.of_string "x"
  | Name x -> x

(* TODO: finish Rec caes *)
let ids_of_glob_constr c =
  let rec ids_of_glob_constr acc {loc; CAst.v = c} =
    let idof = id_of_name in
    match c with
      | GVar id -> id::acc
      | GApp (g,args) ->
          ids_of_glob_constr [] g @ List.flatten (List.map (ids_of_glob_constr []) args) @ acc
      | GLambda (na,k,ty,c) -> idof na :: ids_of_glob_constr [] ty @ ids_of_glob_constr [] c @ acc
      | GProd (na,k,ty,c) -> idof na :: ids_of_glob_constr [] ty @ ids_of_glob_constr [] c @ acc
      | GLetIn (na,b,t,c) -> idof na :: ids_of_glob_constr [] b @ Option.cata (ids_of_glob_constr []) [] t @ ids_of_glob_constr [] c @ acc
      | GCast (c,(CastConv t|CastVM t|CastNative t)) -> ids_of_glob_constr [] c @ ids_of_glob_constr [] t @ acc
      | GCast (c,CastCoerce) -> ids_of_glob_constr [] c @ acc
      | GIf (c,(na,po),b1,b2) -> ids_of_glob_constr [] c @ ids_of_glob_constr [] b1 @ ids_of_glob_constr [] b2 @ acc
      | GLetTuple (nal,(na,po),b,c) ->
          List.map idof nal @ ids_of_glob_constr [] b @ ids_of_glob_constr [] c @ acc
      | GCases (sty,rtntypopt,tml,brchl) ->
	  List.flatten (List.map (fun (_,(idl,patl,c)) -> idl @ ids_of_glob_constr [] c) brchl)
      | GRec _ -> failwith "Fix inside a constructor branch"
      | (GSort _ | GHole _ | GRef _ | GEvar _ | GPatVar _) -> []
  in
  (* build the set *)
  List.fold_left (fun acc x -> Id.Set.add x acc) Id.Set.empty (ids_of_glob_constr [] c)





let zeta_normalize =
  let rec zeta_normalize_term x = CAst.map (function
      | GRef _
      | GVar _
      | GEvar _
      | GPatVar _ as rt -> rt
      | GApp(rt',rtl) ->
	  GApp(zeta_normalize_term rt',
	       List.map zeta_normalize_term rtl
	      )
      | GLambda(name,k,t,b) ->
	  GLambda(name,
		  k,
		  zeta_normalize_term t,
		  zeta_normalize_term b
		 )
      | GProd(name,k,t,b) ->
	  GProd(name,
	        k,
		zeta_normalize_term t,
		zeta_normalize_term b
		 )
      | GLetIn(Name id,def,typ,b) ->
	  (zeta_normalize_term (replace_var_by_term id def b)).CAst.v
      | GLetIn(Anonymous,def,typ,b) ->
          (zeta_normalize_term b).CAst.v
      | GLetTuple(nal,(na,rto),def,b) ->
	  GLetTuple(nal,
		    (na,Option.map zeta_normalize_term rto),
		    zeta_normalize_term def,
		    zeta_normalize_term b
		   )
      | GCases(sty,infos,el,brl) ->
	  GCases(sty,
		 infos,
		 List.map (fun (e,x) -> (zeta_normalize_term e,x)) el,
		 List.map zeta_normalize_br brl
		)
      | GIf(b,(na,e_option),lhs,rhs) ->
	  GIf(zeta_normalize_term b,
	      (na,Option.map zeta_normalize_term e_option),
	      zeta_normalize_term lhs,
	      zeta_normalize_term rhs
	     )
      | GRec _ -> raise (UserError(None,str "Not handled GRec"))
      | GSort _
      | GHole _ as rt -> rt
      | GCast(b,c) ->
	  GCast(zeta_normalize_term b,
                Miscops.map_cast_type zeta_normalize_term c)
    ) x
  and zeta_normalize_br (loc,(idl,patl,res)) =
    (loc,(idl,patl,zeta_normalize_term res))
  in
  zeta_normalize_term




let expand_as =

  let rec add_as map ({loc; CAst.v = pat } as rt) =
    match pat with
      | PatVar _ -> map
      | PatCstr(_,patl,Name id) ->
	  Id.Map.add id (pattern_to_term rt) (List.fold_left add_as map patl)
      | PatCstr(_,patl,_) -> List.fold_left add_as map patl
  in
  let rec expand_as map = CAst.map (function
      | GRef _ | GEvar _ | GPatVar _ | GSort _ | GHole _ as rt -> rt
      | GVar id as rt ->
	  begin
	    try
	      (Id.Map.find id map).CAst.v
	    with Not_found -> rt
	  end
      | GApp(f,args) -> GApp(expand_as map f,List.map (expand_as map) args)
      | GLambda(na,k,t,b) -> GLambda(na,k,expand_as map t, expand_as map b)
      | GProd(na,k,t,b) -> GProd(na,k,expand_as map t, expand_as map b)
      | GLetIn(na,v,typ,b) -> GLetIn(na, expand_as map v,Option.map (expand_as map) typ,expand_as map b)
      | GLetTuple(nal,(na,po),v,b) ->
	  GLetTuple(nal,(na,Option.map (expand_as map) po),
		    expand_as map v, expand_as map b)
      | GIf(e,(na,po),br1,br2) ->
	  GIf(expand_as map e,(na,Option.map (expand_as map) po),
	      expand_as map br1, expand_as map br2)
      | GRec _ ->  user_err Pp.(str "Not handled GRec")
      | GCast(b,c) ->
	  GCast(expand_as map b,
		Miscops.map_cast_type (expand_as map) c)
      | GCases(sty,po,el,brl) ->
	  GCases(sty, Option.map (expand_as map) po, List.map (fun (rt,t) -> expand_as map rt,t) el,
		List.map (expand_as_br map) brl)
    )
  and expand_as_br map (loc,(idl,cpl,rt)) =
    (loc,(idl,cpl, expand_as (List.fold_left add_as map cpl) rt))
  in
  expand_as Id.Map.empty



           
(* [resolve_and_replace_implicits ?expected_type env sigma rt] solves implicits of [rt] w.r.t. [env] and [sigma] and then replace them by their solution 
 *)

exception Found of Evd.evar_info
let resolve_and_replace_implicits ?(flags=Pretyping.all_and_fail_flags) ?(expected_type=Pretyping.WithoutTypeConstraint) env sigma rt =
  let open Evd in
  let open Evar_kinds in 
  (* we first (pseudo) understand [rt] and get back the computed evar_map *)
  (* FIXME : JF (30/03/2017) I'm not completely sure to have split understand as needed. 
If someone knows how to prevent solved existantial removal in  understand, please do not hesitate to change the computation of [ctx] here *) 
  let ctx,_ = Pretyping.ise_pretype_gen flags env sigma Glob_ops.empty_lvar expected_type rt in
  let ctx, f = Evarutil.nf_evars_and_universes ctx in

  (* then we map [rt] to replace the implicit holes by their values *)
  let rec change rt =
    match rt.CAst.v with
    | GHole(ImplicitArg(grk,pk,bk),_,_) -> (* we only want to deal with implicit arguments *)
       (
         try (* we scan the new evar map to find the evar corresponding to this hole (by looking the source *)
           Evd.fold (* to simulate an iter *)
             (fun _ evi _ ->
               match evi.evar_source with
               | (loc_evi,ImplicitArg(gr_evi,p_evi,b_evi)) ->
                  if Globnames.eq_gr grk gr_evi && pk=p_evi && bk=b_evi  && rt.CAst.loc = loc_evi
                  then raise (Found evi)
               | _ -> ()
             )
             ctx
             ();
           (* the hole was not solved : we do nothing *)
           rt
         with Found evi -> (* we found the evar corresponding to this hole *)
           match evi.evar_body with
           | Evar_defined c ->
           (* we just have to lift the solution in glob_term *)
              Detyping.detype false [] env ctx (EConstr.of_constr (f c))
           | Evar_empty -> rt (* the hole was not solved : we do nothing *)
       )
    | _ -> Glob_ops.map_glob_constr change rt 
  in
  change rt
