
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Term
open Constant
open Inductive
open Instantiate
open Reduction
open Libobject
open Lib
open Declare
open Classops
open Class
open Recordops

let recalc_sp sp =
  let (_,spid,k) = repr_path sp in Lib.make_path spid k

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

let process_constant (ids_to_discard,work_alist) cb =
  failwith "todo"

let process_inductive (ids_to_discard,work_alist) mib =
  failwith "todo"

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
	  let ((_,spid,spk)) = repr_path sp in
	  let ce = process_constant (ids_to_discard,work_alist) cb in
	  declare_constant spid (ce,stre);
          (ids_to_discard,work_alist)
	end
	  
    | "INDUCTIVE" ->
	let mib = Global.lookup_mind sp in
	let ((_,spid,spk)) = repr_path sp in
	let mie = process_inductive (ids_to_discard,work_alist) mib in
	let _ = declare_mind mie in
        (ids_to_discard,work_alist)

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
