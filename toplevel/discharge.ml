
(* $Id$ *)

open Pp
open Util
open Names
open Sign
open Generic
open Term
open Declarations
open Inductive
open Instantiate
open Reduction
open Typeops
open Libobject
open Lib
open Declare
open Classops
open Class
open Recordops

let recalc_sp sp =
  let (_,spid,k) = repr_path sp in Lib.make_path spid k

(* Abstractions. *)

let whd_all c = whd_betadeltaiota (Global.env()) Evd.empty c

let generalize_type id var c =
  typed_product_without_universes (Name id) var (typed_app (subst_var id) c)

type modification_action = ABSTRACT | ERASE

let interp_modif absfun oper (oper',modif) cl = 
  let rec interprec = function
    | ([], cl) -> DOPN(oper',Array.of_list cl)
    | (ERASE::tlm, c::cl) -> interprec (tlm,cl)
    | (ABSTRACT::tlm, c::cl) -> absfun (interprec (tlm,cl)) c
    | _ -> assert false
  in 
  interprec (modif,cl)

type 'a modification =
  | NOT_OCCUR
  | DO_ABSTRACT of 'a * modification_action list
  | DO_REPLACE

let modify_opers replfun absfun oper_alist =
  let failure () =
    anomalylabstrm "generic__modify_opers"
      [< 'sTR"An oper which was never supposed to appear has just appeared" ;
         'sPC ; 'sTR"Either this is in system code, and you need to" ; 'sPC;
         'sTR"report this error," ; 'sPC ;
         'sTR"Or you are using a user-written tactic which calls" ; 'sPC ;
         'sTR"generic__modify_opers, in which case the user-written code" ;
         'sPC ; 'sTR"is broken - this function is an internal system" ;
         'sPC ; 'sTR"for internal system use only" >]
  in
  let rec substrec = function
    (* Hack pour ls sp dans l'annotation du Cases *)
    | DOPN(MutCase(n,(spi,a,b,c,d)) as oper,cl) ->
	let cl' = Array.map substrec cl in
	(try
	   match List.assoc (MutInd spi) oper_alist with
	     | DO_ABSTRACT (MutInd spi',_) ->
		 DOPN(MutCase(n,(spi',a,b,c,d)),cl')
	     | _ -> raise Not_found
	 with
	   | Not_found -> DOPN(oper,cl'))
    | DOPN(oper,cl) as c ->
	let cl' = Array.map substrec cl in
	(try
	   (match List.assoc oper oper_alist with
	      | NOT_OCCUR -> failure ()
	      | DO_ABSTRACT (oper',modif) ->
		  if List.length modif > Array.length cl then
		    anomaly "found a reference with too few args"
		  else 
		    interp_modif absfun oper (oper',modif) (Array.to_list cl')
	      | DO_REPLACE -> substrec (replfun (DOPN(oper,cl'))))
	 with 
	   | Not_found -> DOPN(oper,cl'))
    | DOP1(i,c) -> DOP1(i,substrec c)
    | DOPL(oper,cl) -> DOPL(oper,List.map substrec cl)
    | DOP2(oper,c1,c2) -> DOP2(oper,substrec c1,substrec c2)
    | DLAM(na,c) -> DLAM(na,substrec c)
    | DLAMV(na,v) -> DLAMV(na,Array.map substrec v)
    | x -> x
  in 
  if oper_alist = [] then fun x -> x else substrec

(**)

let under_dlams f = 
  let rec apprec = function 
    | DLAMV(na,c) -> DLAMV(na,Array.map f c)
    | DLAM(na,c)  -> DLAM(na,apprec c)
    | _           -> failwith "under_dlams"
  in 
  apprec 

let abstract_inductive ids_to_abs hyps inds =
  let abstract_one_var id ty inds =
    let ntyp = List.length inds in 
    let new_refs = list_tabulate (fun k -> applist(Rel (k+2),[Rel 1])) ntyp in 
    let inds' =
      List.map
      	(function (tname,arity,cnames,lc) -> 
	   let arity' = generalize_type id ty arity in
	   let lc' =
	     List.map
	       (fun b -> generalize_type id ty (typed_app (substl new_refs) b))
	       lc
	   in
           (tname,arity',cnames,lc'))
      	inds
    in 
    (inds',ABSTRACT)
  in
  let abstract_once ((hyps,inds,modl) as sofar) id =
    if isnull_sign hyps or id <> fst (hd_sign hyps) then 
      sofar
    else
      let (inds',modif) = abstract_one_var id (snd (hd_sign hyps)) inds in 
      (tl_sign hyps,inds',modif::modl)
  in
  let (_,inds',revmodl) =
    List.fold_left abstract_once (hyps,inds,[]) ids_to_abs in
  let inds'' =
    List.map 
      (fun (a,b,c,d) -> (a,body_of_type b,c,List.map body_of_type d))
      inds' in
  (inds'', List.rev revmodl)

let abstract_constant ids_to_abs hyps (body,typ) =
  let abstract_once ((hyps,body,typ,modl) as sofar) id =
    if isnull_sign hyps or id <> fst(hd_sign hyps) then 
      sofar
    else
      let name = Name id in
      let var = snd (hd_sign hyps) in
      let cvar = incast_type var in
      let body' = match body with
	| None -> None
	| Some { contents = Cooked c } -> 
	    Some (ref (Cooked (mkLambda name cvar (subst_var id c))))
	| Some { contents = Recipe f } ->
	    Some (ref (Recipe 
			 (fun () -> mkLambda name cvar (subst_var id (f())))))
      in
      let typ' = generalize_type id var typ in
      (tl_sign hyps,body',typ',ABSTRACT::modl)
  in
  let (_,body',typ',revmodl) =
    List.fold_left abstract_once (hyps,body,typ,[]) ids_to_abs in
  (body',typ', List.rev revmodl)


(* Substitutions. *)

let expmod_constr oldenv modlist c =
  let sigma = Evd.empty in
  let simpfun = 
    if modlist = [] then fun x -> x else nf_betaiota oldenv sigma in
  let expfun cst = 
    try 
      constant_value oldenv cst
    with Failure _ ->
      let (sp,_) = destConst cst in
      errorlabstrm "expmod_constr"
	[< 'sTR"Cannot unfold the value of " ;
           'sTR(string_of_path sp) ; 'sPC;
           'sTR"You cannot declare local lemmas as being opaque"; 'sPC;
           'sTR"and then require that theorems which use them"; 'sPC;
           'sTR"be transparent" >];
  in
  let under_casts f = function
    | DOP2(Cast,c,t) -> (DOP2(Cast,f c,f t))
    | c -> f c 
  in
  let c' = modify_opers expfun (fun a b -> mkAppL [|a; b|]) modlist c in
  match c' with
    | DOP2 (Cast,val_0,typ) -> DOP2 (Cast,simpfun val_0,simpfun typ)
    | _ -> simpfun c'

let expmod_type oldenv modlist c = 
  typed_app (expmod_constr oldenv modlist) c

let expmod_constant_value opaque oldenv modlist = function
  | None -> None
  | Some { contents = Cooked c } -> 
      if opaque then 
	(* None *)
        Some (ref (Recipe (fun () -> expmod_constr oldenv modlist c)))
      else
	Some (ref (Cooked (expmod_constr oldenv modlist c)))
  | Some { contents = Recipe f } -> 
      Some (ref (Recipe (fun () -> expmod_constr oldenv modlist (f ()))))


(* Discharge of inductive types. *)

let process_inductive osecsp nsecsp oldenv (ids_to_discard,modlist) mib =
  assert (Array.length mib.mind_packets > 0);
  let finite = mib.mind_packets.(0).mind_finite in
  let inds = 
    array_map_to_list
      (fun mip ->
	 (mip.mind_typename,
	  make_typed_lazy 
	    (expmod_constr oldenv modlist (mind_user_arity mip))
	    (fun _ -> level_of_type mip.mind_nf_arity),
	  Array.to_list mip.mind_consnames,
	  Array.to_list
	    (array_map2
	       (fun us nfc ->
		  make_typed_lazy 
		    (expmod_constr oldenv modlist us)
		    (fun _ -> level_of_type nfc))
	       (mind_user_lc mip) mip.mind_nf_lc)))
      mib.mind_packets
  in
  let (inds',modl) = abstract_inductive ids_to_discard mib.mind_hyps inds in
  let lmodif_one_mind i = 
    let nbc = Array.length (mind_nth_type_packet mib i).mind_consnames in 
    (MutInd(osecsp,i),DO_ABSTRACT(MutInd(nsecsp,i),modl))::
    (list_tabulate
       (function j -> 
	  let j' = j + 1 in
	  (MutConstruct((osecsp,i),j'),
	   DO_ABSTRACT(MutConstruct((nsecsp,i),j'),modl)))
       nbc) 
  in
  let modifs = List.flatten (list_tabulate lmodif_one_mind mib.mind_ntypes) in 
  ({ mind_entry_nparams = mib.mind_nparams + (List.length modl);
     mind_entry_finite = finite;
     mind_entry_inds = inds' },
   modifs)


(* Discharge of constants. *)

let process_constant osecsp nsecsp oldenv (ids_to_discard,modlist) cb =
  let body = 
    expmod_constant_value cb.const_opaque oldenv modlist cb.const_body in
  let typ = expmod_type oldenv modlist cb.const_type in
  let hyps = map_sign_typ (expmod_type oldenv modlist) cb.const_hyps in
  let (body',typ',modl) = abstract_constant ids_to_discard hyps (body,typ) in
  let mods = [ (Const osecsp, DO_ABSTRACT(Const nsecsp,modl)) ] in
  (body', body_of_type typ', mods)


(* Discharge of the various objects of the environment. *)

let constant_message id =
  if Options.is_verbose() then 
    pPNL [< print_id id; 'sTR " is discharged." >]

let inductive_message inds =
  if Options.is_verbose() then 
    pPNL (hOV 0 
	    (match inds with
	       | [] -> assert false
	       | [(i,_,_,_)] -> [< print_id i; 'sTR " is discharged." >]
	       | l -> [< prlist_with_sep pr_coma 
			   (fun (id,_,_,_) -> print_id id) l;
			 'sPC; 'sTR "are discharged.">]))

type discharge_operation = 
  | Variable of identifier * constr * strength * bool
  | Parameter of identifier * constr
  | Constant of identifier * constant_entry * strength
  | Inductive of mutual_inductive_entry
  | Class of cl_typ * cl_info_typ
  | Struc of inductive_path * struc_typ
  | Coercion of ((coe_typ * coe_info_typ) * cl_typ * cl_typ) 
              * identifier * int 

let process_object oldenv sec_sp (ops,ids_to_discard,work_alist) (sp,lobj) =
  let tag = object_tag lobj in 
  match tag with
    | "VARIABLE" ->
	let (id,a,stre,sticky) = out_variable sp in
	if stre = (DischargeAt sec_sp) or ids_to_discard <> [] then
	  (ops,id::ids_to_discard,work_alist)
	else
	  let expmod_a = expmod_constr oldenv work_alist (body_of_type a) in
	  (Variable (id,expmod_a,stre,sticky) :: ops,
           ids_to_discard,work_alist)

    | "CONSTANT" | "PARAMETER" ->
	let stre = constant_or_parameter_strength sp in
	if stre = (DischargeAt sec_sp) then
	  (ops, ids_to_discard, (Const sp, DO_REPLACE) :: work_alist)
	else
	  let cb = Environ.lookup_constant sp oldenv in
	  let spid = basename sp in
	  let newsp = recalc_sp sp in
	  let (body,typ,mods) = 
	    process_constant sp newsp oldenv (ids_to_discard,work_alist) cb in
	  let op = match body with
	    | None -> 
		Parameter (spid,typ)
	    | Some { contents = b } -> 
		let ce = 
		  { const_entry_body = b; const_entry_type = Some typ } in
		Constant (spid,ce,stre)
	  in
          (op::ops, ids_to_discard, mods@work_alist)
  
    | "INDUCTIVE" ->
	let mib = Environ.lookup_mind sp oldenv in
	let newsp = recalc_sp sp in
	let (mie,mods) = 
	  process_inductive sp newsp oldenv (ids_to_discard,work_alist) mib in
        ((Inductive mie)::ops, ids_to_discard, mods@work_alist)

    | "CLASS" -> 
	let ((cl,clinfo) as x) = outClass lobj in
	if clinfo.cL_STRE = (DischargeAt sec_sp) then 
	  (ops,ids_to_discard,work_alist)
	else
	  let (y1,y2) = process_class sec_sp x in
          ((Class (y1,y2))::ops, ids_to_discard, work_alist)
	  
    | "COERCION" -> 
	let (((_,coeinfo),_,_)as x) = outCoercion lobj in
        if coeinfo.cOE_STRE = (DischargeAt sec_sp) then 
	  (ops,ids_to_discard,work_alist)
        else
	  let (y,idf,ps) = process_coercion sec_sp x in
          ((Coercion (y,idf,ps))::ops, ids_to_discard, work_alist)
                    
    | "STRUCTURE" ->
	let ((sp,i),info) = outStruc lobj in
	let newsp = recalc_sp sp in
	let mib = Environ.lookup_mind sp oldenv in
	let strobj =
	  { s_CONST = info.s_CONST;
	    s_PARAM = mib.mind_nparams;
	    s_PROJ = List.map (option_app recalc_sp) info.s_PROJ } in
	((Struc ((newsp,i),strobj))::ops, ids_to_discard, work_alist)

    (***TODO
    | "OBJDEF1" -> 
	let sp = outObjDef1 lobj in
        let ((_,spid,_)) = repr_path sp in
        begin try objdef_declare spid with _ -> () end;
        (ids_to_discard,work_alist)
    ***)

    | _ -> (ops,ids_to_discard,work_alist)

let process_item oldenv sec_sp acc = function
  | (sp,Leaf lobj) -> process_object oldenv sec_sp acc (sp,lobj)
  | (_,_) -> acc

let process_operation = function
  | Variable (id,expmod_a,stre,sticky) ->
      declare_variable id (expmod_a,stre,sticky)
  | Parameter (spid,typ) ->
      declare_parameter spid typ;
      constant_message spid
  | Constant (spid,ce,stre) ->
      declare_constant spid (ce,stre);
      constant_message spid
  | Inductive mie ->
      let _ = declare_mind mie in
      inductive_message mie.mind_entry_inds
  | Class (y1,y2) ->
      Lib.add_anonymous_leaf (inClass (y1,y2))
  | Struc (newsp,strobj) ->
      Lib.add_anonymous_leaf (inStruc (newsp,strobj))
  | Coercion ((_,_,clt) as y,idf,ps) ->
      Lib.add_anonymous_leaf (inCoercion y) 

let close_section _ s = 
  let oldenv = Global.env() in
  let (sec_sp,decls) = close_section s in
  let (ops,ids,_) = 
    List.fold_left (process_item oldenv sec_sp) ([],[],[]) decls in 
  Global.pop_vars ids;
  List.iter process_operation (List.rev ops)


