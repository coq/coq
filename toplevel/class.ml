
(* $Id$ *)

open Util
open Pp
open Names
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
(*  | (x,y) when (x = NeverDischarge || x = NotDeclare)
            && (y = NeverDischarge || y = NotDeclare) -> false
  | (x,_) when x = NeverDischarge || x = NotDeclare -> false
  | (_,x) when x = NeverDischarge || x = NotDeclare -> true*)

  | (NeverDischarge,_) -> false
  | (NotDeclare,_) -> false
  | (_,NeverDischarge) -> true
  | (_,NotDeclare) -> true
  | (DischargeAt sp1,DischargeAt sp2) ->
      dirpath_prefix_of sp1 sp2 (* was sp_gt but don't understand why - HH *)

let stre_max (stre1,stre2) =
  if stre_gt (stre1,stre2) then stre1 else stre2

let stre_max4 stre1 stre2 stre3 stre4 =
  stre_max ((stre_max (stre1,stre2)),(stre_max (stre3,stre4)))

let id_of_varid c = match kind_of_term c with
  | IsVar id -> id
  | _ -> anomaly "class__id_of_varid"

(* lf liste des variable dont depend la coercion f
   lc liste des variable dont depend la classe source *)

let rec stre_unif_cond = function
  | ([],[]) -> NeverDischarge
  | (v::l,[]) -> variable_strength v
  | ([],v::l) -> variable_strength v
  | (v1::l1,v2::l2) ->
      if v1=v2 then 
	stre_unif_cond (l1,l2)
      else
	let stre1 = (variable_strength v1)
	and stre2 = (variable_strength v2) in 
	stre_max (stre1,stre2)

let stre_of_coe = function
  | NAM_Constant sp -> constant_or_parameter_strength sp
  | NAM_Section_Variable sp -> variable_strength sp
  | NAM_Inductive _ | NAM_Constructor _ -> NeverDischarge 

(* verfications pour l'ajout d'une classe *)

let rec arity_sort a = match kind_of_term a with
  | IsSort (Prop _ | Type _) -> 0
  | IsProd (_,_,c) -> (arity_sort c) +1
  | IsLetIn (_,_,_,c) -> arity_sort c    (* Utile ?? *)
  | IsCast (c,_) -> arity_sort c
  | _ -> raise Not_found

let check_fully_applied cl p p1 =
  if p <> p1 then  errorlabstrm "fully_applied" 
    [< 'sTR"Wrong number of parameters for ";'sTR(string_of_class cl) >]
	
(* try_add_class : Names.identifier ->
  Term.constr -> (cl_typ * int) option -> bool -> int * Libobject.strength *)

let try_add_class v (cl,p) streopt check_exist = 
  if check_exist & class_exists cl then
    errorlabstrm "try_add_new_class" 
      [< 'sTR (string_of_class cl) ; 'sTR " is already a class" >];
  let stre' = stre_of_cl cl in 
  let stre = match streopt with
    | Some stre -> stre_max (stre,stre')
    | None -> stre'
  in
  add_new_class (cl,stre,p);
  stre

(* try_add_new_class : Names.identifier -> unit *)

let try_add_new_class ref stre =
  let v = constr_of_reference Evd.empty (Global.env()) ref in
  let env = Global.env () in
  let t = Retyping.get_type_of env Evd.empty v in
  let p1 =
    try 
      arity_sort t 
    with Not_found -> 
      errorlabstrm "try_add_class" 
        [< 'sTR "Type of "; Printer.pr_global ref;
           'sTR " does not end with a sort" >] 
  in
  let cl = fst (constructor_at_head v) in
  let _ = try_add_class v (cl,p1) (Some stre) true in () 

(* check_class : Names.identifier ->
  Term.constr -> cl_typ -> int -> int * Libobject.strength *)

let check_class v cl p =
  try 
    let _,clinfo = class_info cl in
    check_fully_applied cl p clinfo.cL_PARAM;
    clinfo.cL_STRE
  with Not_found -> 
    let env = Global.env () in
    let t = Retyping.get_type_of env Evd.empty v in
    let p1 =
      try 
	arity_sort t 
      with Not_found -> 
	errorlabstrm "check_class" 
          [< 'sTR "Type of "; 'sTR (string_of_class cl);
             'sTR " does not end with a sort" >] 
    in
    check_fully_applied cl p p1;
    try_add_class v (cl,p1) None false

(* check that the computed target is the provided one *)
let check_target clt = function
    | None -> ()
    | Some cl -> 
	if cl <> clt then 
	  errorlabstrm "try_add_coercion" 
            [<'sTR"Found target class "; 'sTR(string_of_class cl);
	      'sTR " while "; 'sTR(string_of_class clt);
	      'sTR " is expected" >]

(* decomposition de constr vers coe_typ *)

(* t provient de global_reference donc pas de Cast, pas de App *)
let coe_of_reference t = 
  match kind_of_term t with
    | IsConst (sp,l) -> (Array.to_list l),NAM_Constant sp
    | IsMutInd (ind_sp,l) -> (Array.to_list l),NAM_Inductive ind_sp
    | IsMutConstruct (cstr_sp,l) -> (Array.to_list l),NAM_Constructor cstr_sp
    | IsVar id  ->
	let sp =
	  try find_section_variable id 
	  with Not_found -> anomaly "Not a reference"
	in [],NAM_Section_Variable sp
    |  _ -> anomaly "Not a reference"

let constructor_at_head1 t = 
  let rec aux t' =
    match kind_of_term t' with
      | IsConst (sp,l) -> t',[],(Array.to_list l),CL_CONST sp,0
      | IsMutInd (ind_sp,l) -> t',[],(Array.to_list l),CL_IND ind_sp,0
      | IsVar id -> t',[],[],CL_SECVAR (find_section_variable id),0
      | IsCast (c,_) -> aux c
      | IsApp(f,args) -> 
	  let t',_,l,c,_ = aux f in t',Array.to_list args,l,c,Array.length args
      | IsProd (_,_,_) -> t',[],[],CL_FUN,0
      | IsLetIn (_,_,_,c) -> aux c
      | IsSort _ -> t',[],[],CL_SORT,0
      |  _ -> raise Not_found
  in 
  aux (collapse_appl t)


(* condition d'heritage uniforme *)

let uniform_cond nargs lt = 
  let rec aux = function
    | (0,[]) -> true
    | (n,t::l) -> (strip_outer_cast t = mkRel n) & (aux ((n-1),l))
    | _ -> false
  in 
  aux (nargs,lt)

let id_of_cl  = function
  | CL_FUN -> (id_of_string "FUNCLASS")
  | CL_SORT -> (id_of_string "SORTCLASS") 
  | CL_CONST sp -> (basename sp)
  | CL_IND (sp,i) ->
      (mind_nth_type_packet (Global.lookup_mind sp) i).mind_typename
  | CL_SECVAR sp -> (basename sp)

let class_of_ref = function
  | ConstRef sp -> CL_CONST sp
  | IndRef sp -> CL_IND sp
  | VarRef sp -> CL_SECVAR sp
  | ConstructRef _ as c -> 
      errorlabstrm "class_of_ref"
	[< 'sTR "Constructors, such as "; Printer.pr_global c; 
	   'sTR " cannot be used as class" >]
  | EvarRef _ -> 
      errorlabstrm "class_of_ref"
	[< 'sTR "Existential variables cannot be used as class" >]
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
	let (v1,lv1,l,cl1,p1) =
	  match lp with
	    | [] -> raise Not_found
            | t1::_ ->
		try constructor_at_head1 t1
                with _ -> raise Not_found
        in 
	(cl1,p1,v1,lv1,1,l)
    | Some cl ->
	let rec aux n = function
	  | [] -> raise Not_found
	  | t1::lt ->
	      try 
		let v1,lv1,l,cl1,p1 = constructor_at_head1 t1 in
		if cl1 = cl then cl1,p1,v1,lv1,n,l
		else aux (n+1) lt
              with _ -> aux (n + 1) lt
	in aux 1 lp

let get_target t ind =
  if (ind > 1) then 
    CL_FUN,0,t
  else 
    let v2,_,_,cl2,p2 = constructor_at_head1 t in cl2,p2,v2

let prods_of t = 
  let rec aux acc d = match kind_of_term d with
    | IsProd (_,c1,c2) -> aux (c1::acc) c2
    | IsCast (c,_) -> aux acc c
    | _ -> d::acc
  in 
  aux [] t

(* coercion identité *)

let error_not_transparent source =
  errorlabstrm "build_id_coercion"
    [< 'sTR ((string_of_class source)^" must be a transparent constant") >]

let build_id_coercion idf_opt source =
  let env = Global.env () in
  let vs = match source with
    | CL_CONST sp -> constr_of_reference Evd.empty env (ConstRef sp)
    | _ -> error_not_transparent source in
  let c = match Instantiate.constant_opt_value env (destConst vs) with
    | Some c -> c
    | None -> error_not_transparent source in
  let lams,t = Sign.decompose_lam_assum c in
  let llams = List.length lams in
  let lams = List.rev lams in
  let val_f =
    it_mkLambda_or_LetIn
      (mkLambda (Name (id_of_string "x"),
		 applistc vs (rel_list 0 llams),
		 mkRel 1))
       lams
  in
  let typ_f =
    it_mkProd_wo_LetIn
      (mkProd (Anonymous, applistc vs (rel_list 0 llams), lift 1 t))
      lams
  in
  (* juste pour verification *)
  let _ = 
    try 
      Reduction.conv_leq env Evd.empty
	(Typing.type_of env Evd.empty val_f) typ_f
    with _ -> 
      error ("cannot be defined as coercion - "^
	     "maybe a bad number of arguments") 
  in
  let idf =
    match idf_opt with
      | Some idf -> idf
      | None ->
	  id_of_string ("Id_"^(string_of_class source)^"_"^
                        (string_of_class (fst (constructor_at_head t)))) 
  in
  let constr_entry = (* Cast is necessary to express [val_f] is identity *)
    ConstantEntry
      { const_entry_body = mkCast (val_f, typ_f);
	const_entry_type = None } in
  let sp = declare_constant idf (constr_entry,NeverDischarge,false) in
  ConstRef sp

let add_new_coercion_in_graph1 (coef,v,stre,isid,cls,clt) ps =
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
  let v = constr_of_reference Evd.empty env idf in
  let vj = Retyping.get_judgment_of env Evd.empty v in
  let f_vardep,coef = coe_of_reference v in
  if coercion_exists coef then
    errorlabstrm "try_add_coercion" 
      [< Printer.pr_global idf; 'sTR" is already a coercion" >];
  let lp = prods_of (vj.uj_type) in
  let llp = List.length lp in
  if llp <= 1 then
    errorlabstrm "try_add_coercion"         
      [< 'sTR"Does not correspond to a coercion" >];
  let (cls,ps,vs,lvs,ind,s_vardep) =
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
      [< Printer.pr_global idf;
         'sTR" does not respect the inheritance uniform condition" >];
  let clt,pt,vt =
    try 
      get_target (List.hd lp) ind 
    with Not_found -> 
      errorlabstrm "try_add_coercion" 
        [<'sTR"We cannot find the target class" >] 
  in
  check_target clt target;
  let stres = check_class vs cls ps in
  let stret = check_class vt clt pt in
  let stref = stre_of_coe coef in
(* 01/00: Supprimé la prise en compte de la force des variables locales. Sens ?
  let streunif = stre_unif_cond (s_vardep,f_vardep) in
 *)
  let streunif = NeverDischarge in
  let stre' = stre_max4 stres stret stref streunif in
  (* if (stre=NeverDischarge) & (stre'<>NeverDischarge)
     then errorlabstrm "try_add_coercion" 
     [< pr_global idf;
     'sTR" must be declared as a local coercion (its strength is ";
     'sTR(string_of_strength stre');'sTR")" >] *)
  let stre = stre_max (stre,stre') in
  add_new_coercion_in_graph1 (coef,vj,stre,isid,cls,clt) ps


let try_add_new_coercion ref stre =
  try_add_new_coercion_core ref stre None None false

let try_add_new_coercion_subclass cl stre =
  let coe_ref = build_id_coercion None cl in
  try_add_new_coercion_core coe_ref stre (Some cl) None true

let try_add_new_coercion_with_target ref stre source target =
  try_add_new_coercion_core ref stre (Some source) (Some target) false

let try_add_new_identity_coercion id stre source target =
  let ref = build_id_coercion (Some id) source in
  try_add_new_coercion_core ref stre (Some source) (Some target) true

let try_add_new_coercion_with_source ref stre source =
  try_add_new_coercion_core ref stre (Some source) None false

(* fonctions pour le discharge: plutot sale *)

let count_extra_abstractions hyps ids_to_discard =
  let _,n =
    List.fold_left
      (fun (hyps,n as sofar) id -> 
	 match hyps with
	   | (hyp,None,_)::rest when id = hyp ->(rest, n+1)
	   | _ -> sofar)
      (hyps,0) ids_to_discard
  in n

let defined_in_sec sp sec_sp = dirpath sp = sec_sp

let process_class sec_sp ids_to_discard x =
  let (cl,{cL_STRE=stre; cL_PARAM=p}) = x in
(*  let env = Global.env () in*)
  match cl with 
    | CL_SECVAR _ -> x
    | CL_CONST sp -> 
        if defined_in_sec sp sec_sp then
	  let ((_,spid,spk)) = repr_path sp in
          let newsp = Lib.make_path spid CCI in
	  let hyps = (Global.lookup_constant sp).const_hyps in
	  let n = count_extra_abstractions hyps ids_to_discard in
(*
          let v = global_reference CCI spid in
          let t = Retyping.get_type_of env Evd.empty v in
          let p = arity_sort t in
*)
          (CL_CONST newsp,{cL_STRE=stre;cL_PARAM=p+n})
        else 
	  x
    | CL_IND (sp,i) ->
        if defined_in_sec sp sec_sp then
	  let ((_,spid,spk)) = repr_path sp in
          let newsp = Lib.make_path spid CCI in 
	  let hyps = (Global.lookup_mind sp).mind_hyps in
	  let n = count_extra_abstractions hyps ids_to_discard in
(*
          let v = global_reference CCI spid in
          let t = Retyping.get_type_of env Evd.empty v in
          let p = arity_sort t in
*)
          (CL_IND (newsp,i),{cL_STRE=stre;cL_PARAM=p+n})
        else 
	  x
    | _ -> anomaly "process_class" 

let process_cl sec_sp cl =
  match cl with
    | CL_SECVAR id -> cl
    | CL_CONST sp ->
	if defined_in_sec sp sec_sp then
	  let ((_,spid,spk)) = repr_path sp in
          let newsp = Lib.make_path spid CCI in 
          CL_CONST newsp
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
  (* Buggé: faut mettre à jour le nombre de paramètres dans coeinfo *)
  let s1= process_cl sec_sp s in
  let t1 = process_cl sec_sp t in
  match coe with 
    | NAM_Section_Variable _ -> ((coe,coeinfo),s1,t1)
    | NAM_Constant sp -> 
	if defined_in_sec sp sec_sp then
	  let ((_,spid,spk)) = repr_path sp in
	  let newsp = Lib.make_path spid CCI in
	  ((NAM_Constant newsp,coeinfo),s1,t1)
	else
	  ((coe,coeinfo),s1,t1)
    | NAM_Inductive (sp,i) -> 
	if defined_in_sec sp sec_sp then
	  let ((_,spid,spk)) = repr_path sp in
	  let newsp = Lib.make_path spid CCI in
	  ((NAM_Inductive (newsp,i),coeinfo),s1,t1)
	else
	  ((coe,coeinfo),s1,t1)
    | NAM_Constructor ((sp,i),j) -> 
	if defined_in_sec sp sec_sp then 
	  let ((_,spid,spk)) = repr_path sp in
	  let newsp = Lib.make_path spid CCI in
          (((NAM_Constructor ((newsp,i),j)),coeinfo),s1,t1)
	else
	  ((coe,coeinfo),s1,t1)
