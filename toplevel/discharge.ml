(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util

let close_section _ _ = anomaly "No sections today..."

(*
open Identifier
open Names
open Sign
open Term
open Declarations
open Inductive
open Instantiate
open Reduction
open Cooking
open Typeops
open Libnames
open Libobject
open Lib
open Declare
open Impargs
open Classops
open Class
open Recordops
open Library

let recalc_sp dir sp =
  let (_,spid,k) = repr_path sp in Libnames.make_path dir spid k

let rec find_var id = function
  | [] -> raise Not_found
  | (sp,b,_)::l -> if basename sp = id then b=None else find_var id l

let build_abstract_list hyps ids_to_discard =
  map_succeed 
    (fun id ->
       try
	 if find_var id hyps then ABSTRACT else failwith "caugth"
       with Not_found -> failwith "caugth")
    ids_to_discard

(* Discharge of inductives is done here (while discharge of constants 
   is done by the kernel for efficiency). *)

let abstract_inductive ids_to_abs hyps inds =
  let abstract_one_assum id t inds =
    let ntyp = List.length inds in 
    let new_refs =
      list_tabulate (fun k -> applist(mkRel (k+2),[mkRel 1])) ntyp in
    let inds' =
      List.map
      	(function (np,tname,arity,cnames,lc) -> 
	   let arity' = mkNamedProd id t arity in
	   let lc' =
	     List.map (fun b -> mkNamedProd id t (substl new_refs b)) lc
	   in
           (np,tname,arity',cnames,lc'))
      	inds
    in 
    (inds',ABSTRACT) in
  let abstract_one_def id c inds =
    List.map
      (function (np,tname,arity,cnames,lc) -> 
	 let arity' = replace_vars [id, c] arity in
	 let lc' = List.map (replace_vars [id, c]) lc in
         (np,tname,arity',cnames,lc'))
      inds in
  let abstract_once ((hyps,inds,modl) as sofar) id =
    match hyps with
      | (hyp,None,t as d)::rest when id = hyp ->
	  let (inds',modif) = abstract_one_assum hyp t inds in 
	  (rest, inds', modif::modl)
      | (hyp,Some b,t as d)::rest when id = hyp ->
	  let inds' = abstract_one_def hyp b inds in 
	  (rest, inds', modl)
      | _ -> sofar
  in
  let (_,inds',revmodl) =
    List.fold_left abstract_once (hyps,inds,[]) ids_to_abs in
  let inds'' =
    List.map 
      (fun (nparams,a,arity,c,lc) ->
	 let nparams' = nparams + (List.length revmodl) in
	 let params, short_arity = decompose_prod_n_assum nparams' arity in
	 let shortlc =
	   List.map (fun c -> snd (decompose_prod_n_assum nparams' c))lc in
	 let params' =
	   List.map 
	     (function
		| (Name id,None,p) -> id, LocalAssum p
		| (Name id,Some p,_) -> id, LocalDef p
		| (Anonymous,_,_) -> anomaly"Unnamed inductive local variable")
	     params in
	 { mind_entry_nparams = nparams';
	   mind_entry_params = params';
	   mind_entry_typename = a;
	   mind_entry_arity = short_arity;
	   mind_entry_consnames = c;
	   mind_entry_lc = shortlc })
      inds' in
  (inds'', List.rev revmodl)

let process_inductive osecsp nsecsp oldenv (ids_to_discard,modlist) mib =
  assert (Array.length mib.mind_packets > 0);
  let finite = mib.mind_packets.(0).mind_finite in
  let inds = 
    array_map_to_list
      (fun mip ->
	 let nparams = mip.mind_nparams in
	 let arity = expmod_type oldenv modlist (mind_user_arity mip) in
	 let lc = Array.map (expmod_type oldenv modlist) (mind_user_lc mip) in
	 (nparams,
	  mip.mind_typename,
	  arity,
	  Array.to_list mip.mind_consnames,
	  Array.to_list lc))
      mib.mind_packets
  in
  let hyps = mib.mind_hyps in
  let hyps' = map_named_context (expmod_constr oldenv modlist) hyps in
  let (inds',modl) = abstract_inductive ids_to_discard hyps' inds in
  let lmodif_one_mind i = 
    let nbc = Array.length (mind_nth_type_packet mib i).mind_consnames in 
    (((osecsp,i), DO_ABSTRACT ((nsecsp,i),modl)),
     list_tabulate
       (function j -> 
	  let j' = j + 1 in
	  (((osecsp,i),j'), DO_ABSTRACT (((nsecsp,i),j'),modl)))
      nbc)
  in
  let indmodifs,cstrmodifs =
    List.split (list_tabulate lmodif_one_mind mib.mind_ntypes) in 
  ({ mind_entry_finite = finite;
     mind_entry_inds = inds' },
   indmodifs,
   List.flatten cstrmodifs)

(* Discharge messages. *)

let constant_message id =
  Options.if_verbose pPNL [< pr_id id; 'sTR " is discharged." >]

let inductive_message inds =
  Options.if_verbose 
    pPNL
      (hOV 0 
	 (match inds with
	    | [] -> assert false
	    | [ind] ->
		[< pr_label ind.mind_entry_typename; 'sTR " is discharged." >]
	    | l ->
		[< prlist_with_sep pr_coma 
		     (fun ind -> pr_label ind.mind_entry_typename) l;
		   'sPC; 'sTR "are discharged.">]))

(* Discharge operations for the various objects of the environment. *)

type opacity = bool

type discharge_operation = 
  | Variable of identifier * section_variable_entry * strength * bool * bool
  | Parameter of identifier * constr * bool
  | Constant of identifier * recipe * strength * opacity * bool
  | Inductive of mutual_inductive_entry * bool
  | Class of cl_typ * cl_info_typ
  | Struc of inductive_path * (unit -> struc_typ)
  | Objdef of constant_path
  | Coercion of coercion_entry
  | Require of module_reference

(* Main function to traverse the library segment and compute the various
   discharge operations. *)

let process_object oldenv dir sec_sp
  (ops,ids_to_discard,(constl,indl,cstrl as work_alist)) (sp,lobj) =
  let tag = object_tag lobj in 
  match tag with
    | "VARIABLE" ->
	let ((id,c,t),stre,sticky) = get_variable sp in
	(* VARIABLE means local (entry Variable/Hypothesis/Local and are *)
	(* always discharged *)
(*
 	if stre = (DischargeAt sec_sp) or ids_to_discard <> [] then
*)
	  (ops,id::ids_to_discard,work_alist)
(*
	else
	  let imp = is_implicit_var sp in
	  let newdecl =
	    match c with
	      | None ->
		  SectionLocalAssum
		    (expmod_constr oldenv work_alist (body_of_type t))
	      | Some body ->
		  SectionLocalDef
		    (expmod_constr oldenv work_alist body)
	  in
	  (Variable (id,newdecl,stre,sticky,imp) :: ops,
	   ids_to_discard,work_alist)
*)

    | "CONSTANT" | "PARAMETER" ->
	(* CONSTANT/PARAMETER means never discharge (though visibility *)
	(* may vary) *)
 	let stre = constant_or_parameter_strength sp in
(*
	if stre = (DischargeAt sec_sp) then
	  let cb = Environ.lookup_constant sp oldenv in
	  let constl = (sp, DO_REPLACE cb)::constl in
	  (ops, ids_to_discard, (constl,indl,cstrl))
	else
*)
	  let cb = Environ.lookup_constant sp oldenv in
	  let spid = basename sp in
	  let imp = is_implicit_constant sp in
	  let newsp = recalc_sp dir sp in
	  let mods = 
	    let modl = build_abstract_list cb.const_hyps ids_to_discard in
	    [ (sp, DO_ABSTRACT(newsp,modl)) ]
	  in
	  let r = { d_from = cb;
		    d_modlist = work_alist;
		    d_abstract = ids_to_discard } in
	  let op = Constant (spid,r,stre,cb.const_opaque,imp) in
          (op :: ops, ids_to_discard, (mods@constl, indl, cstrl))
  
    | "INDUCTIVE" ->
	let mib = Environ.lookup_mind sp oldenv in
	let newsp = recalc_sp dir sp in
	let imp = is_implicit_args() (* CHANGE *) in
	let (mie,indmods,cstrmods) = 
	  process_inductive sp newsp oldenv (ids_to_discard,work_alist) mib in
	((Inductive(mie,imp)) :: ops, ids_to_discard,
	 (constl,indmods@indl,cstrmods@cstrl))

    | "CLASS" -> 
	let ((cl,clinfo) as x) = outClass lobj in
	if clinfo.cl_strength = (DischargeAt sec_sp) then 
	  (ops,ids_to_discard,work_alist)
	else
	  let (y1,y2) = process_class sec_sp ids_to_discard x in
          ((Class (y1,y2))::ops, ids_to_discard, work_alist)
	  
    | "COERCION" -> 
	let (((_,coeinfo),_,_)as x) = outCoercion lobj in
        if coercion_strength coeinfo = (DischargeAt sec_sp) then 
	  (ops,ids_to_discard,work_alist)
        else
	  let y = process_coercion sec_sp ids_to_discard x in
          ((Coercion y)::ops, ids_to_discard, work_alist)
                    
    | "STRUCTURE" ->
	let ((sp,i),info) = outStruc lobj in
	let newsp = recalc_sp dir sp in
	let strobj () =
	  let mib = Environ.lookup_mind newsp (Global.env ()) in
	  { s_CONST = info.s_CONST;
	    s_PARAM = (mind_nth_type_packet mib 0).mind_nparams;
	    s_PROJ = List.map (option_app (recalc_sp dir)) info.s_PROJ } in
	((Struc ((newsp,i),strobj))::ops, ids_to_discard, work_alist)

    | "OBJDEF1" -> 
	let sp = outObjDef1 lobj in
	let new_sp = recalc_sp dir sp in
        ((Objdef new_sp)::ops, ids_to_discard, work_alist)

    | "REQUIRE" -> 
	let c = out_require lobj in
	((Require c)::ops, ids_to_discard, work_alist)

    | _ -> (ops,ids_to_discard,work_alist)

let process_item oldenv dir sec_sp acc = function
  | (sp,Leaf lobj) -> process_object oldenv dir sec_sp acc (sp,lobj)
  | (_,_) -> acc

let process_operation = function
  | Variable (id,expmod_a,stre,sticky,imp) ->
      (* Warning:parentheses needed to get a side-effect from with_implicits *)
      let _ = with_implicits imp (declare_variable id) (expmod_a,stre,sticky) in
      ()
  | Parameter (spid,typ,imp) ->
      let _ = with_implicits imp (declare_parameter spid) typ in
      constant_message spid
  | Constant (spid,r,stre,opa,imp) ->
      let _ =
	with_implicits imp (declare_constant spid) (ConstantRecipe r,stre,opa)
      in
      constant_message spid
  | Inductive (mie,imp) ->
      let _ = with_implicits imp declare_mind mie in
      inductive_message mie.mind_entry_inds
  | Class (y1,y2) ->
      Lib.add_anonymous_leaf (inClass (y1,y2))
  | Struc (newsp,strobj) ->
      Lib.add_anonymous_leaf (inStruc (newsp,strobj ()))
  | Objdef newsp ->
      begin try Recordobj.objdef_declare (ConstRef newsp) with _ -> () end
  | Coercion y -> add_new_coercion y
  | Require y -> reload_module y

let catch_not_found f x =
  try f x
  with Not_found ->
    error ("Something is missing; perhaps a reference to a"^
    " module required inside the section")

let close_section _ s = 
  let oldenv = Global.env() in
  let sec_sp,decls,fs = close_section false s in
  let newdir = dirpath sec_sp in
  let olddir = wd_of_sp sec_sp in
  let (ops,ids,_) = 
    if Options.immediate_discharge then ([],[],([],[],[]))
    else
      List.fold_left 
	(process_item oldenv newdir olddir) ([],[],([],[],[])) decls 
  in
  let ids = last_section_hyps olddir in
  Global.pop_named_decls ids;
  Summary.unfreeze_lost_summaries fs;
  add_frozen_state ();
  if Options.immediate_discharge then ()
  else
    catch_not_found (List.iter process_operation) (List.rev ops);
  Nametab.push_section olddir
*)
