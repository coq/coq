
(* $Id$ *)

open Util
open Pp
open Names
open Generic
open Term
open Inductive
open Declarations
open Environ
open Lib
open Classops
open Declare

(* manipulations concernant les strength *)

(* gt dans le sens de "longueur du sp" (donc le moins persistant) *)

(* strength * strength -> bool *)

let stre_gt = function
  | (NeverDischarge,NeverDischarge) -> false
  | (NeverDischarge,x) -> false
  | (x,NeverDischarge) -> true
  | (DischargeAt sp1,DischargeAt sp2) -> sp_gt (sp1,sp2) 

let stre_max (stre1,stre2) =
  if stre_gt (stre1,stre2) then stre1 else stre2

let stre_max4 stre1 stre2 stre3 stre4 =
  stre_max ((stre_max (stre1,stre2)),(stre_max (stre3,stre4)))

let id_of_varid = function
  | VAR id -> id
  | _ -> anomaly "class__id_of_varid"

let stre_of_VAR c = variable_strength (destVar c)

(* lf liste des variable dont depend la coercion f
   lc liste des variable dont depend la classe source *)

let rec stre_unif_cond = function
  | ([],[]) -> NeverDischarge
  | (v::l,[]) -> stre_of_VAR v
  | ([],v::l) -> stre_of_VAR v
  | (v1::l1,v2::l2) ->
      if v1=v2 then 
	stre_unif_cond (l1,l2)
      else
	let stre1 = (stre_of_VAR v1)
	and stre2 = (stre_of_VAR v2) in 
	stre_max (stre1,stre2)

let stre_of_coe = function
  | NAM_Constant sp -> constant_strength sp
  | NAM_Var id -> variable_strength id
  | NAM_Inductive _ | NAM_Constructor _ -> NeverDischarge 
	
(* try_add_class : Names.identifier ->
  Term.constr -> (cl_typ * int) option -> bool -> int * Libobject.strength *)

let try_add_class id v clpopt streopt check_exist = 
  let env = Global.env () in
  let t = Retyping.get_type_of env Evd.empty v in
  let p1 =
    try 
      arity_sort t 
    with Not_found -> 
      errorlabstrm "try_add_class" 
        [< 'sTR "Type of "; 'sTR (string_of_id id);
           'sTR " does not end with a sort" >] 
  in
  let cl,p =
    match clpopt with
      | None -> let (cl,_)=constructor_at_head v in (cl,p1)
      | Some (cl,p2) -> (fully_applied id p2 p1;cl,p1) 
  in
  if check_exist & class_exists cl then
    errorlabstrm "try_add_new_class" 
      [< 'sTR (string_of_id id) ; 'sTR " is already a class" >];
  let stre' = stre_of_cl cl in 
  let stre = match streopt with
    | Some stre -> stre_max (stre,stre')
    | None -> stre'
  in
  add_new_class (cl,(string_of_id id),stre,p);
  stre

(* try_add_new_class : Names.identifier -> unit *)

let try_add_new_class id stre =
  let v = global_reference CCI id in
  let _ = try_add_class id v None (Some stre) true in () 

(* check_class : Names.identifier ->
  Term.constr -> cl_typ -> int -> int * Libobject.strength *)

let check_class id v cl p =
  try 
    let _,clinfo = class_info cl in
    if p = clinfo.cL_PARAM then 
      clinfo.cL_STRE
    else 
      errorlabstrm "fully_applied" 
	[< 'sTR"Wrong number of parameters for ";'sTR(string_of_id id) >]
  with Not_found -> 
    try_add_class id v (Some (cl,p)) None false


(* decomposition de constr vers coe_typ *)

(* t provient de global_reference donc pas de Cast, pas de AppL *)
let coe_of_reference t = 
  match kind_of_term t with
    | IsConst (sp,l) -> (Array.to_list l),NAM_Constant sp
    | IsMutInd (ind_sp,l) -> (Array.to_list l),NAM_Inductive ind_sp
    | IsMutConstruct (cstr_sp,l) -> (Array.to_list l),NAM_Constructor cstr_sp
    | IsVar id  -> [],NAM_Var id
    |  _ -> anomaly "Not a reference"

let constructor_at_head1 t = 
  let rec aux t' =
    match kind_of_term t' with
      | IsConst (sp,l) -> t',[],(Array.to_list l),CL_SP sp,0
      | IsMutInd (ind_sp,l) -> t',[],(Array.to_list l),CL_IND ind_sp,0
      | IsVar id -> t',[],[],CL_Var id,0
      | IsCast (c,_) -> aux c
      | IsAppL(f,args) -> 
	  let t',_,l,c,_ = aux f in t',args,l,c,List.length args
      | IsProd (_,_,_) -> t',[],[],CL_FUN,0
      | IsSort _ -> t',[],[],CL_SORT,0
      |  _ -> raise Not_found
  in 
  aux (collapse_appl t)


(* condition d'heritage uniforme *)

let uniform_cond nargs lt = 
  let rec aux = function
    | (0,[]) -> true
    | (n,t::l) -> (strip_outer_cast t = Rel n) & (aux ((n-1),l))
    | _ -> false
  in 
  aux (nargs,lt)

let id_of_cl  = function
  | CL_FUN -> (id_of_string "FUNCLASS")
  | CL_SORT -> (id_of_string "SORTCLASS") 
  | CL_SP sp -> (basename sp)
  | CL_IND (sp,i) ->
      (mind_nth_type_packet (Global.lookup_mind sp) i).mind_typename
  | CL_Var id -> id 
	
let string_of_cl  = function
  | CL_FUN -> "FUNCLASS"
  | CL_SORT -> "SORTCLASS" 
  | CL_SP sp -> string_of_id (basename sp)
  | CL_IND (sp,i) ->
      string_of_id
	(mind_nth_type_packet (Global.lookup_mind sp) i).mind_typename
  | CL_Var id -> string_of_id id 

(* 
lp est la liste (inverse'e) des arguments de la coercion
ids est le nom de la classe source
sps_opt est le sp de la classe source dans le cas des structures
retourne:
la classe souce
nbre d'arguments de la classe
le constr de la class
l'indice de la classe source dans la liste lp
la liste des variables dont depend la classe source
*)

let get_source lp source =
  match source with
    | None ->
	let (v1,lv1,l,cl1,p1) as x =
	  match lp with
	    | [] -> raise Not_found
            | t1::_ ->
		try constructor_at_head1 t1
                with _ -> raise Not_found
        in 
	(id_of_cl cl1),(cl1,p1,v1,lv1,1,l)
    | Some id -> 
	let rec aux n = function
	  | [] -> raise Not_found
	  | t1::lt ->
	      try 
		let v1,lv1,l,cl1,p1 = constructor_at_head1 t1 in
		if id_of_cl cl1 = id then cl1,p1,v1,lv1,n,l
		else aux (n+1) lt
              with _ -> aux (n + 1) lt
	in id, aux 1 lp

let get_target t ind =
  if (ind > 1) then 
    CL_FUN,0,t
  else 
    let v2,_,_,cl2,p2 = constructor_at_head1 t in cl2,p2,v2

let prods_of t = 
  let rec aux acc = function
    | DOP2(Prod,c1,DLAM(_,c2)) -> aux (c1::acc) c2
    | (DOP2(Cast,c,_)) -> aux acc c
    | t -> t::acc
  in 
  aux [] t

(* coercion identite' *)

let lams_of t = 
  let rec aux acc = function
    | DOP2(Lambda,c1,DLAM(x,c2)) -> aux ((x,c1)::acc) c2
    | DOP2(Cast,c,_) -> aux acc c
    | t -> acc,t
  in 
  aux [] t

let build_id_coercion idf_opt ids =
  let env = Global.env () in
  let vs = construct_reference env CCI ids in 
  let c = match (strip_outer_cast vs) with
    | (DOPN(Const sp,l) as c') when Environ.evaluable_constant env c' ->
	(try Instantiate.constant_value env c'
         with _ -> errorlabstrm "build_id_coercion"
             [< 'sTR(string_of_id ids);
		'sTR" must be a transparent constant" >])
    | _ -> 
	errorlabstrm "build_id_coercion"
          [< 'sTR(string_of_id ids); 
	     'sTR" must be a transparent constant" >] 
  in
  let lams,t = lams_of c in
  let lams = List.rev lams in
  let llams = List.length lams in
  let val_f =
    List.fold_right
      (fun (x,t) u -> DOP2(Lambda,t,DLAM(x,u)))
      lams
      (DOP2(Lambda,(applistc vs (rel_list 0 llams)),
	    DLAM(Name (id_of_string "x"),Rel 1))) 
  in
  let typ_f =
    List.fold_right
      (fun (x,t) c -> DOP2(Prod,t,DLAM(x,c)))
      lams
      (DOP2(Prod,(applistc vs (rel_list 0 llams)),
	    DLAM(Anonymous,lift 1 t))) 
  in 
  let constr_f = DOP2(Cast,val_f,typ_f) in
  (* juste pour verification *)
  let _ = 
    try 
      Typing.type_of env Evd.empty constr_f
    with _ -> 
      error ("cannot be defined as coercion - "^
	     "may be a bad number of arguments") 
  in
  let idf =
    match idf_opt with
      | Some(idf) -> idf
      | None ->
	  id_of_string ("Id_"^(string_of_id ids)^"_"^
                        (string_of_cl (fst (constructor_at_head t)))) 
  in
  let constr_entry = 
    { const_entry_body = Cooked constr_f; const_entry_type = None } in
  declare_constant idf (constr_entry,NeverDischarge);
  idf

let add_new_coercion_in_graph1 (coef,v,stre,isid,cls,clt) idf ps =
  add_anonymous_leaf
    (inCoercion
       ((coef,
	 {cOE_VALUE=v;cOE_STRE=stre;cOE_ISID=isid;cOE_PARAM=ps}),
	cls,clt))

(* 
nom de la fonction coercion
strength de f
nom de la classe source (optionnel)
sp de la classe source (dans le cas des structures)
nom de la classe target (optionnel)
booleen "coercion identite'?"

lorque source est None alors target est None aussi.
*)

let try_add_new_coercion_core idf stre source target isid =
  let env = Global.env () in
  let v = construct_reference env CCI idf in
  let t = Retyping.get_type_of env Evd.empty v in
  let k = Retyping.get_type_of env Evd.empty t in
  let vj = {uj_val=v; uj_type=t; uj_kind = k} in
  let f_vardep,coef = coe_of_reference v in
  if coercion_exists coef then
    errorlabstrm "try_add_coercion" 
      [< 'sTR(string_of_id idf) ; 'sTR" is already a coercion" >];
  let lp = prods_of t in
  let llp = List.length lp in
  if llp <= 1 then
    errorlabstrm "try_add_coercion"         
      [< 'sTR"Does not correspond to a coercion" >];
  let ids,(cls,ps,vs,lvs,ind,s_vardep) =
    try 
      get_source (List.tl lp) source
    with Not_found -> 
      errorlabstrm "try_add_coercion" 
        [<'sTR"We do not find the source class " >] 
  in
  if (cls = CL_FUN) then
    errorlabstrm "try_add_coercion" 
      [< 'sTR"FUNCLASS cannot be a source class" >];
  if (cls = CL_SORT) then
    errorlabstrm "try_add_coercion" 
      [< 'sTR"SORTCLASS cannot be a source class" >];
  if not (uniform_cond (llp-1-ind) lvs) then
    errorlabstrm "try_add_coercion" 
      [<'sTR(string_of_id idf);
        'sTR" does not respect the inheritance uniform condition" >];
  let clt,pt,vt =
    try 
      get_target (List.hd lp) ind 
    with Not_found -> 
      errorlabstrm "try_add_coercion" 
        [<'sTR"We cannot find the target class" >] 
  in
  let idt =
    (match target with
       | Some idt -> 
	   if idt = id_of_cl clt then 
	     idt
	   else 
	     errorlabstrm "try_add_coercion" 
               [<'sTR"The target class does not correspond to ";
		 'sTR(string_of_id idt) >]
       | None -> (id_of_cl clt)) 
  in
  let stres = check_class ids vs cls ps in
  let stret = check_class idt vt clt pt in
  let stref = stre_of_coe coef in
(* 01/00: Supprimé la prise en compte de la force des variables locales. Sens ?
  let streunif = stre_unif_cond (s_vardep,f_vardep) in
 *)
  let streunif = NeverDischarge in
  let stre' = stre_max4 stres stret stref streunif in
  (* if (stre=NeverDischarge) & (stre'<>NeverDischarge)
     then errorlabstrm "try_add_coercion" 
     [<'sTR(string_of_id idf);
     'sTR" must be declared as a local coercion (its strength is ";
     'sTR(string_of_strength stre');'sTR")" >] *)
  let stre = stre_max (stre,stre') in
  add_new_coercion_in_graph1 (coef,vj,stre,isid,cls,clt) idf ps


let try_add_new_coercion id stre =
  try_add_new_coercion_core id stre None None false

let try_add_new_coercion_subclass id stre =
  let idf = build_id_coercion None id in
  try_add_new_coercion_core idf stre (Some id) None true

let try_add_new_coercion_with_target id stre source target isid =
  if isid then
    let idf = build_id_coercion (Some id) source in
    try_add_new_coercion_core idf stre (Some source) (Some target) true
  else 
    try_add_new_coercion_core id stre (Some source) (Some target) false

let try_add_new_coercion_record id stre source =
  try_add_new_coercion_core id stre (Some source) None false

(* fonctions pour le discharge: plutot sale *)

let defined_in_sec sp sec_sp =
  let ((p1,id1,k1)) = repr_path sp in
  let ((p2,id2,k2)) = repr_path sec_sp in
  p1 = (string_of_id id2)::p2

let process_class sec_sp ((cl,{cL_STR=s;cL_STRE=stre;cL_PARAM=p}) as x ) =
  let env = Global.env () in
  match cl with 
    | CL_Var id -> x
    | CL_SP sp -> 
        if defined_in_sec sp sec_sp then
	  let ((_,spid,spk)) = repr_path sp in
          let newsp = Lib.make_path spid CCI in 
          let v = global_reference CCI spid in
          let t = Retyping.get_type_of env Evd.empty v in
          let p = arity_sort t in
          (CL_SP newsp,{cL_STR=s;cL_STRE=stre;cL_PARAM=p})
        else 
	  x
    | CL_IND (sp,i) ->
        if defined_in_sec sp sec_sp then
	  let ((_,spid,spk)) = repr_path sp in
          let newsp = Lib.make_path spid CCI in 
          let v = global_reference CCI spid in
          let t = Retyping.get_type_of env Evd.empty v in
          let p = arity_sort t in
          (CL_IND (newsp,i),{cL_STR=s;cL_STRE=stre;cL_PARAM=p})
        else 
	  x
    | _ -> anomaly "process_class" 

let process_cl sec_sp cl =
  match cl with
    | CL_Var id -> CL_Var id 
    | CL_SP sp ->
	if defined_in_sec sp sec_sp then
	  let ((_,spid,spk)) = repr_path sp in
          let newsp = Lib.make_path spid CCI in 
          CL_SP newsp
        else 
	  cl
    | CL_IND (sp,i) ->
	if defined_in_sec sp sec_sp then
	  let ((_,spid,spk)) = repr_path sp in
          let newsp = Lib.make_path spid CCI in 
          CL_IND (newsp,i)
        else 
	  cl
    | _ -> cl

(* Pour le discharge *)
let process_coercion sec_sp (((coe,coeinfo),s,t) as x) =
  let s1= process_cl sec_sp s in
  let t1 = process_cl sec_sp t in
  let p = (snd (class_info s1)).cL_PARAM in
  match coe with 
    | NAM_Var id -> ((coe,coeinfo),s1,t1),id,p
    | NAM_Constant sp -> 
	if defined_in_sec sp sec_sp then
	  let ((_,spid,spk)) = repr_path sp in
	  let newsp = Lib.make_path spid CCI in
	  ((NAM_Constant newsp,coeinfo),s1,t1),spid,p
	else
	  ((coe,coeinfo),s1,t1),basename sp,p
    | NAM_Inductive (sp,i) -> 
	if defined_in_sec sp sec_sp then
	  let ((_,spid,spk)) = repr_path sp in
	  let newsp = Lib.make_path spid CCI in
	  ((NAM_Inductive (newsp,i),coeinfo),s1,t1),spid,p
	else
	  ((coe,coeinfo),s1,t1),basename sp,p
    | NAM_Constructor ((sp,i),j) -> 
	if defined_in_sec sp sec_sp then 
	  let ((_,spid,spk)) = repr_path sp in
	  let newsp = Lib.make_path spid CCI in
	  let id = Global.id_of_global (MutConstruct((newsp,i),j)) in
          (((NAM_Constructor ((newsp,i),j)),coeinfo),s1,t1),id,p
	else
	  ((coe,coeinfo),s1,t1),
	  Global.id_of_global (MutConstruct((sp,i),j)),
	  p
