
(* $Id$ *)

open Pp
open Util
open Names
open Sign
open Generic
open Term
open Constant
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
  let c' = mkProd (Name id) var.body (subst_var id c.body) in
  let c'ty = sort_of_product_without_univ var.typ c.typ in 
  { body = c'; typ = c'ty }

let casted_generalize id var c =
  let c' = mkProd (Name id) var.body (subst_var id (cast_term c)) in
  let s = destSort (whd_all (cast_type c)) in
  let c'ty = sort_of_product_without_univ var.typ s in 
  mkCast c' (DOP0 (Sort c'ty))

let abstract_inductive ids_to_abs hyps inds =
  let abstract_one_var id ty inds =
    let ntyp = List.length inds in 
    let new_refs = list_tabulate (fun k -> applist(Rel (k+2),[Rel 1])) ntyp in 
    let inds' =
      List.map
      	(function (tname,arity,cnames,lc) -> 
	   let arity' = generalize_type id ty arity in
	   let lc' =
	     under_dlams 
               (fun b -> casted_generalize id ty (substl new_refs b)) lc
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
  let inds'' = List.map (fun (a,b,c,d) -> (a,b.body,c,d)) inds' in
  (inds'', List.rev revmodl)

let abstract_constant ids_to_abs hyps (body,typ) =
  let abstract_once ((hyps,body,typ,modl) as sofar) id =
    if isnull_sign hyps or id <> fst(hd_sign hyps) then 
      sofar
    else
      let name = Name id in
      let var = snd (hd_sign hyps) in
      let cvar = incast_type var in
      let body' = mkLambda name cvar (subst_var id body) in
      let typ' =
    	{ body = mkProd name cvar (subst_var id typ.body);
	  typ  = sort_of_product_without_univ var.typ typ.typ } 
      in
      (tl_sign hyps,body',typ',ABSTRACT::modl)
  in
  let (_,body',typ',revmodl) =
    List.fold_left abstract_once (hyps,body,typ,[]) ids_to_abs in
  (body',typ', List.rev revmodl)


(* Substitutions. *)

let expmod_constr modlist c =
  let env = Global.env() in
  let sigma = Evd.empty in
  let simpfun = if modlist = [] then fun x -> x else nf_betaiota env sigma in
  let expfun c = 
    let (sp,_) = destConst c in 
    try 
      constant_value env c
    with Failure _ -> begin
      mSGERRNL 
	[< 'sTR"Cannot unfold the value of " ;
           'sTR(string_of_path sp) ; 'sPC;
           'sTR"You cannot declare local lemmas as being opaque"; 'sPC;
           'sTR"and then require that theorems which use them"; 'sPC;
           'sTR"be transparent" >];
      let cb = Global.lookup_constant sp in
      cb.const_opaque <- false;
      (try
         let v = constant_value env c in 
	 cb.const_opaque <- true; 
	 v
       with _ -> anomaly "expmod_constr")
    end
  in
  let under_casts f = function
    | DOP2(Cast,c,t) -> (DOP2(Cast,f c,f t))
    | c -> f c 
  in
  let c' = modify_opers expfun (fun a b -> mkAppL [|a; b|]) modlist c in
  match c' with
    | DOP2(Cast,val_0,typ) -> DOP2(Cast,simpfun val_0,simpfun typ)
    | DOP2(XTRA "IND",c,DLAMV(na,lc)) ->
	DOP2(XTRA "IND",under_casts simpfun c,
             DLAMV(na,Array.map (under_casts simpfun) lc))
    | _ -> simpfun c'

let expmod_type modlist {body=c;typ=s} = {body=expmod_constr modlist c;typ=s}


(* Discharge of inductive types. *)

let process_inductive osecsp nsecsp (ids_to_discard,modlist) mib =
  assert (Array.length mib.mind_packets > 0);
  let finite = mib.mind_packets.(0).mind_finite in
  let inds = 
    array_map_to_list
      (fun mip ->
	 (mip.mind_typename,
	  expmod_type modlist mip.mind_arity,
	  Array.to_list mip.mind_consnames,
	  under_dlams (expmod_constr modlist) mip.mind_lc))
      mib.mind_packets
  in
  let (inds',modl) = abstract_inductive ids_to_discard mib.mind_hyps inds in
  let lmodif_one_mind i = 
    let nbc = Array.length (mind_nth_type_packet mib i).mind_consnames in 
    (MutInd(osecsp,i),DO_ABSTRACT(MutInd(nsecsp,i),modl))::
    (MutCase(Some (osecsp,i)),DO_ABSTRACT(MutCase(Some (nsecsp,i)),[]))::
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

let process_constant osecsp nsecsp (ids_to_discard,modlist) cb =
  let body = global_reference CCI (basename osecsp) in
  let typ = expmod_type modlist cb.const_type in
  let (body',typ',modl) = 
    abstract_constant ids_to_discard cb.const_hyps (body,typ)
  in
  let mods = (Const osecsp, DO_ABSTRACT(Const nsecsp,modl)) :: modlist in
  ({ const_entry_body = body'; const_entry_type = Some typ'.body },
   mods)


(* Discharge of the various objects of the environment. *)

let constant_message sp =
  if Options.verbose() then 
    pPNL [< print_id (basename sp); 'sTR " is discharged." >]

let inductive_message inds =
  if Options.verbose() then 
    pPNL (hOV 0 
	    (match inds with
	       | [] -> assert false
	       | [(i,_,_,_)] -> [< print_id i; 'sTR " is discharged." >]
	       | l -> [< prlist_with_sep pr_coma 
			   (fun (id,_,_,_) -> print_id id) l;
			 'sPC; 'sTR "are discharged.">]))

let process_object sec_sp (ids_to_discard,work_alist) (sp,lobj) =
  let tag = object_tag lobj in 
  match tag with
    | "VARIABLE" ->
	let (id,a,stre,sticky) = out_variable sp in
	if stre = (DischargeAt sec_sp) or ids_to_discard <> [] then
	  (id::ids_to_discard,work_alist)
	else begin
	  let expmod_a = expmod_constr work_alist a.body in
	  declare_variable id (expmod_a,stre,sticky);
          (ids_to_discard,work_alist)
	end

    | "CONSTANT" ->
	let stre = constant_strength sp in
	if stre = (DischargeAt sec_sp) then
	  (ids_to_discard, (Const sp, DO_REPLACE) :: work_alist)
	else begin
	  let cb = Global.lookup_constant sp in
	  let spid = basename sp in
	  let newsp = recalc_sp sp in
	  let (ce,mods) = 
	    process_constant sp newsp (ids_to_discard,work_alist) cb in
	  declare_constant spid (ce,stre);
	  constant_message sp;
          (ids_to_discard,mods@work_alist)
	end
  
    | "INDUCTIVE" ->
	let mib = Global.lookup_mind sp in
	let newsp = recalc_sp sp in
	let (mie,mods) = 
	  process_inductive sp newsp (ids_to_discard,work_alist) mib in
	let _ = declare_mind mie in
	inductive_message mie.mind_entry_inds;
        (ids_to_discard,mods@work_alist)

    | "CLASS" -> 
	let ((cl,clinfo) as x) = outClass lobj in
	if clinfo.cL_STRE = (DischargeAt sec_sp) then 
	  (ids_to_discard,work_alist)
	else begin 
	  let y = process_class sec_sp x in
          Lib.add_anonymous_leaf (inClass y);
          (ids_to_discard,work_alist)
	end
	  
    | "COERCION" -> 
	let (((_,coeinfo),_,_)as x) = outCoercion lobj in
        if coeinfo.cOE_STRE = (DischargeAt sec_sp) then 
	  (ids_to_discard,work_alist)
        else begin 
	  let ((_,_,clt) as y),idf,ps = process_coercion sec_sp x in
          Lib.add_anonymous_leaf (inCoercion y); 
          coercion_syntax idf ps clt;
          (ids_to_discard,work_alist)
	end
                    
    | "STRUCTURE" ->
	let (sp,info) = outStruc lobj in
	let newsp = recalc_sp sp in
	let mib = Global.lookup_mind (ccisp_of newsp) in
	let strobj =
	  { s_CONST= info.s_CONST;
	    s_PARAM= mib.mind_nparams;
	    s_PROJ= List.map (option_app recalc_sp) info.s_PROJ} in
	Lib.add_anonymous_leaf (inStruc (newsp,strobj));
	(ids_to_discard,work_alist)

    (***TODO
    | "OBJDEF1" -> 
	let sp = outObjDef1 lobj in
        let ((_,spid,_)) = repr_path sp in
        begin try objdef_declare spid with _ -> () end;
        (ids_to_discard,work_alist)
    ***)

    | _ -> 
	(ids_to_discard,work_alist)

let process_item sec_sp acc = function
  | (sp,Leaf lobj) -> process_object sec_sp acc (sp,lobj)
  | (_,_) -> acc

let close_section _ s = 
  let (sec_sp,decls) = close_section s in
  let _ = List.fold_left (process_item sec_sp) ([],[]) decls in 
  ()
