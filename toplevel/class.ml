(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Pp
open Identifier
open Names
open Term
open Inductive
open Declarations
open Environ
open Inductive
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
      is_dirpath_prefix_of sp1 sp2
	(* was sp_gt but don't understand why - HH *)

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

let stre_of_global = function
  | ConstRef sp -> constant_or_parameter_strength sp
  | VarRef sp -> variable_strength sp
  | IndRef _ | ConstructRef _ -> NeverDischarge 

(* verfications pour l'ajout d'une classe *)

let rec arity_sort a = match kind_of_term a with
  | IsSort (Prop _ | Type _) -> 0
  | IsProd (_,_,c) -> (arity_sort c) +1
  | IsLetIn (_,_,_,c) -> arity_sort c    (* Utile ?? *)
  | IsCast (c,_) -> arity_sort c
  | _ -> raise Not_found

(* try_add_class : Names.identifier ->
  Term.constr -> (cl_typ * int) option -> bool -> int * Libobject.strength *)

let try_add_class v (cl,p) streopt check_exist = 
  if check_exist & class_exists cl then
    errorlabstrm "try_add_new_class" 
      [< 'sTR (string_of_class cl) ; 'sTR " is already a class" >];
  let stre' = strength_of_cl cl in 
  let stre = match streopt with
    | Some stre -> stre_max (stre,stre')
    | None -> stre'
  in
  declare_class (cl,stre,p)

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

(* Coercions *)

type coercion_error_kind =
  | AlreadyExists
  | NotACoercion
  | NoSource of string
  | NotUniform
  | NoTarget
  | WrongTarget of cl_typ * cl_typ
  | NotAClass of cl_typ
  | NotEnoughClassArgs of cl_typ

exception CoercionError of coercion_error_kind

let explain_coercion_error g = function
  | AlreadyExists ->
      errorlabstrm "try_add_coercion" 
	[< Printer.pr_global g; 'sTR" is already a coercion" >]
  | NotACoercion ->
      errorlabstrm "try_add_coercion"         
	[< Printer.pr_global g; 'sTR" does not correspond to a coercion" >]
  | NoSource s ->
    errorlabstrm "try_add_coercion" 
      [< Printer.pr_global g; 'sTR ": "; 'sTR s >]
  | NotUniform ->
    errorlabstrm "try_add_coercion" 
      [< Printer.pr_global g;
         'sTR" does not respect the inheritance uniform condition" >];
  | NoTarget ->
      errorlabstrm "try_add_coercion" 
        [<'sTR"We cannot find the target class" >]
  | WrongTarget (clt,cl) ->
      errorlabstrm "try_add_coercion" 
        [<'sTR"Found target class "; 'sTR(string_of_class cl);
	  'sTR " while "; 'sTR(string_of_class clt);
	  'sTR " is expected" >]
  | NotAClass cl ->
	errorlabstrm "check_class" 
          [< 'sTR "Type of "; 'sTR (string_of_class cl);
             'sTR " does not end with a sort" >] 
  | NotEnoughClassArgs cl ->
      errorlabstrm "fully_applied" 
	[< 'sTR"Wrong number of parameters for ";'sTR(string_of_class cl) >]

let check_fully_applied cl p p1 =
  if p <> p1 then raise (CoercionError (NotEnoughClassArgs cl))

(* check_class : Names.identifier ->
  Term.constr -> cl_typ -> int -> int * Libobject.strength *)

let check_class v cl p =
  try 
    let _,clinfo = class_info cl in
    check_fully_applied cl p clinfo.cl_param
  with Not_found -> 
    let env = Global.env () in
    let t = Retyping.get_type_of env Evd.empty v in
    let p1 =
      try 
	arity_sort t 
      with Not_found -> raise (CoercionError (NotAClass cl))
    in
    check_fully_applied cl p p1;
    try_add_class v (cl,p1) None false

(* check that the computed target is the provided one *)
let check_target clt = function
  | Some cl when cl <> clt -> raise (CoercionError (WrongTarget(clt,cl)))
  | _ -> ()

(* decomposition de constr vers coe_typ *)

(* t provient de global_reference donc pas de Cast, pas de App *)
let coe_of_reference t = 
  match kind_of_term t with
    | IsConst (sp,l) -> (Array.to_list l), ConstRef sp
    | IsMutInd (ind_sp,l) -> (Array.to_list l), IndRef ind_sp
    | IsMutConstruct (cstr_sp,l) -> (Array.to_list l), ConstructRef cstr_sp
    | IsVar id  ->
	let sp =
	  try find_section_variable id 
	  with Not_found -> anomaly "Not a reference"
	in [], VarRef sp
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
      ident_of_label (mind_nth_type_packet (Global.lookup_mind sp) i).mind_typename
  | CL_SECVAR id -> id

let class_of_ref = function
  | ConstRef sp -> CL_CONST sp
  | IndRef sp -> CL_IND sp
  | VarRef sp -> CL_SECVAR sp
  | ConstructRef _ as c -> 
      errorlabstrm "class_of_ref"
	[< 'sTR "Constructors, such as "; Printer.pr_global c; 
	   'sTR " cannot be used as class" >]

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

let get_strength stre ref cls clt =
  let stres = (snd (class_info cls)).cl_strength in
  let stret = (snd (class_info clt)).cl_strength in
  let stref = stre_of_global ref in
(* 01/00: Supprim� la prise en compte de la force des variables locales. Sens ?
  let streunif = stre_unif_cond (s_vardep,f_vardep) in
 *)
  let streunif = NeverDischarge in
  let stre' = stre_max4 stres stret stref streunif in
  if (stre = NeverDischarge) & (stre' <> NeverDischarge)
  then errorlabstrm "try_add_coercion" 
    [< Printer.pr_global ref;
       'sTR " must be declared as a local coercion"; 'fNL;
       'sTR "because it involves local definition" >];
  stre_max (stre,stre')

(* coercion identit� *)

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
  let val_f =
    it_mkLambda_or_LetIn
      (mkLambda (Name (id_of_string "x"),
		 applistc vs (extended_rel_list 0 lams),
		 mkRel 1))
       lams
  in
  let typ_f =
    it_mkProd_wo_LetIn
      (mkProd (Anonymous, applistc vs (extended_rel_list 0 lams), lift 1 t))
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
      { const_entry_body = Some (mkCast (val_f, typ_f));
	const_entry_type = None } in
  let sp = declare_constant idf (constr_entry,NeverDischarge,false) in
  ConstRef sp

(* 
nom de la fonction coercion
strength de f
nom de la classe source (optionnel)
sp de la classe source (dans le cas des structures)
nom de la classe target (optionnel)
booleen "coercion identite'?"

lorque source est None alors target est None aussi.
*)

let add_new_coercion_core idf stre source target isid =
  let env = Global.env () in
  let v = constr_of_reference Evd.empty env idf in
  let vj = Retyping.get_judgment_of env Evd.empty v in
  (* coef, c'est idf non ?
  let f_vardep,coef = coe_of_reference v in
  *)
  let coef = idf in
  if coercion_exists coef then raise (CoercionError AlreadyExists);
  let lp = prods_of (vj.uj_type) in
  let llp = List.length lp in
  if llp <= 1 then raise (CoercionError NotACoercion);
  let (cls,ps,vs,lvs,ind,s_vardep) =
    try 
      get_source (List.tl lp) source
    with Not_found ->
      raise (CoercionError (NoSource "Cannot find the source class "))
  in
  if (cls = CL_FUN) then
    raise (CoercionError (NoSource "FUNCLASS cannot be a source class"));
  if (cls = CL_SORT) then
    raise (CoercionError (NoSource "SORTCLASS cannot be a source class"));
  if not (uniform_cond (llp-1-ind) lvs) then
    raise (CoercionError NotUniform);
  let clt,pt,vt =
    try
      get_target (List.hd lp) ind 
    with Not_found ->
      raise (CoercionError NoTarget)
  in
  check_target clt target;
  check_class vs cls ps;
  check_class vt clt pt;
  let stre' = get_strength stre coef cls clt in
  declare_coercion coef vj stre' isid cls clt ps

let try_add_new_coercion_core ref b c d e =
  try add_new_coercion_core ref b c d e
  with CoercionError e -> explain_coercion_error ref e

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

(* fonctions pour le discharge: encore un peu sale mais �a s'am�liore *)

type coercion_entry = 
    global_reference * strength * bool * cl_typ * cl_typ * int

let add_new_coercion (ref,stre,isid,cls,clt,n) =
  (* Un peu lourd, tout cela pour trouver l'instance *)
  let env = Global.env () in
  let v = constr_of_reference Evd.empty env ref in
  let vj = Retyping.get_judgment_of env Evd.empty v in
  declare_coercion ref vj stre isid cls clt n

let count_extra_abstractions hyps ids_to_discard =
  let _,n =
    List.fold_left
      (fun (hyps,n as sofar) id -> 
	 match hyps with
	   | (hyp,None,_)::rest when id = basename hyp ->(rest, n+1)
	   | _ -> sofar)
      (hyps,0) ids_to_discard
  in n

let defined_in_sec ref sec_sp = 
  snd (Libnames.repr_qualid (Nametab.get_full_qualid ref)) = sec_sp

(* This moves the global path one step below *)
let process_global _ = 
  anomaly "I forgot sections ... :("
(*
  | VarRef _ ->
      anomaly "process_global only processes global surviving the section"
  | ConstRef ln ->
      let id = ident_of_label (label ln) in
      let newsp = Lib.make_path spid CCI in
      ConstRef newsp
  | IndRef (sp,i) -> 
      let ((_,spid,spk)) = repr_path sp in
      let newsp = Lib.make_path spid CCI in
      IndRef (newsp,i)
  | ConstructRef ((sp,i),j) -> 
      let ((_,spid,spk)) = repr_path sp in
      let newsp = Lib.make_path spid CCI in
      ConstructRef ((newsp,i),j)
*)

let process_class sec_sp ids_to_discard x =
  anomaly "Eer, I forgot sections..."

(*  let (cl,{cl_strength=stre; cl_param=p}) = x in
(*  let env = Global.env () in*)
  match cl with 
    | CL_SECVAR _ -> x
    | CL_CONST cp -> 
        if defined_in_sec (ConstRef cp) sec_sp then
	  let ((_,spid,spk)) = repr_path sp in
          let newsp = Lib.make_path spid CCI in
	  let hyps = (Global.lookup_constant cp).const_hyps in
	  let n = count_extra_abstractions hyps ids_to_discard in
(*
          let v = global_reference CCI spid in
          let t = Retyping.get_type_of env Evd.empty v in
          let p = arity_sort t in
*)
          (CL_CONST newsp,{cl_strength=stre;cl_param=p+n})
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
          (CL_IND (newsp,i),{cl_strength=stre;cl_param=p+n})
        else 
	  x
    | _ -> anomaly "process_class" 
*)

let process_cl sec_sp cl =
  anomaly "I forgot sections"
(*  match cl with
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
*)
let process_coercion sec_sp ids_to_discard ((coe,coeinfo),cls,clt) =
  anomaly "Now sections!!! Ha ha ha!!!"
(*
  let hyps = context_of_global_reference coe in let nargs =
  count_extra_abstractions hyps ids_to_discard in (process_global coe,
  coercion_strength coeinfo, coercion_identity coeinfo, process_cl
  sec_sp cls, process_cl sec_sp clt, nargs + coercion_params coeinfo)
*)
