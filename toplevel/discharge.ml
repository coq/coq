
(* $Id$ *)

open Pp
open Util
open Names
open Sign
open Term
open Declarations
open Inductive
open Instantiate
open Reduction
open Cooking
open Typeops
open Libobject
open Lib
open Declare
open Impargs
open Classops
open Class
open Recordops

let recalc_sp dir sp =
  let (_,spid,k) = repr_path sp in Names.make_path dir spid k

let build_abstract_list hyps ids_to_discard =
  map_succeed 
    (fun id -> 
       if not (mem_named_context id hyps) then failwith "caugth"; ABSTRACT)
    ids_to_discard

(* Discharge of inductives is done here (while discharge of constants 
   is done by the kernel for efficiency). *)

let abstract_inductive ids_to_abs hyps inds =
  let abstract_one_var d inds =
    let ntyp = List.length inds in 
    let new_refs =
      list_tabulate (fun k -> applist(mkRel (k+2),[mkRel 1])) ntyp in
    let inds' =
      List.map
      	(function (tname,arity,cnames,lc) -> 
	   let arity' = mkNamedProd_or_LetIn d arity in
	   let lc' =
	     List.map (fun b -> mkNamedProd_or_LetIn d (substl new_refs b)) lc
	   in
           (tname,arity',cnames,lc'))
      	inds
    in 
    (inds',ABSTRACT)
  in
  let abstract_once ((hyps,inds,modl) as sofar) id =
    match hyps with
      | [] -> sofar
      | (hyp,c,t as d)::rest ->
	  if id <> hyp then sofar
	  else
	    let (inds',modif) = abstract_one_var d inds in 
	    (rest, inds', modif::modl)
  in
  let (_,inds',revmodl) =
    List.fold_left abstract_once (hyps,inds,[]) ids_to_abs in
  let inds'' =
    List.map 
      (fun (a,b,c,d) -> (a,body_of_type b,c,List.map body_of_type d))
      inds' in
  (inds'', List.rev revmodl)

let process_inductive osecsp nsecsp oldenv (ids_to_discard,modlist) mib =
  assert (Array.length mib.mind_packets > 0);
  let finite = mib.mind_packets.(0).mind_finite in
  let inds = 
    array_map_to_list
      (fun mip ->
	 (mip.mind_typename,
	  expmod_type oldenv modlist (mind_user_arity mip),
	  Array.to_list mip.mind_consnames,
	  Array.to_list
	    (Array.map (expmod_type oldenv modlist) (mind_user_lc mip))))
      mib.mind_packets
  in
  let hyps' = map_named_context (expmod_constr oldenv modlist) mib.mind_hyps in
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
  ({ mind_entry_nparams = mib.mind_nparams + (List.length modl);
     mind_entry_finite = finite;
     mind_entry_inds = inds' },
   indmodifs,
   List.flatten cstrmodifs)

(* Discharge messages. *)

let constant_message id =
  if Options.is_verbose() then pPNL [< print_id id; 'sTR " is discharged." >]

let inductive_message inds =
  if Options.is_verbose() then 
    pPNL (hOV 0 
	    (match inds with
	       | [] -> assert false
	       | [(i,_,_,_)] -> [< print_id i; 'sTR " is discharged." >]
	       | l -> [< prlist_with_sep pr_coma 
			   (fun (id,_,_,_) -> print_id id) l;
			 'sPC; 'sTR "are discharged.">]))

(* Discharge operations for the various objects of the environment. *)

type discharge_operation = 
  | Variable of identifier * section_variable_entry * strength * bool * bool
  | Parameter of identifier * constr * bool
  | Constant of identifier * recipe * strength * bool
  | Inductive of mutual_inductive_entry * bool
  | Class of cl_typ * cl_info_typ
  | Struc of inductive_path * struc_typ
  | Coercion of ((coe_typ * coe_info_typ) * cl_typ * cl_typ) 
              * identifier * int 

(* Main function to traverse the library segment and compute the various
   discharge operations. *)

let process_object oldenv dir sec_sp
  (ops,ids_to_discard,(constl,indl,cstrl as work_alist)) (sp,lobj) =
  let tag = object_tag lobj in 
  match tag with
    | "VARIABLE" ->
	let ((id,c,t),stre,sticky) = get_variable sp in
	if stre = (DischargeAt sec_sp) or ids_to_discard <> [] then
	  (ops,id::ids_to_discard,work_alist)
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

    | "CONSTANT" | "PARAMETER" ->
	let stre = constant_or_parameter_strength sp in
	if stre = (DischargeAt sec_sp) then
	  let constl = (sp, DO_REPLACE)::constl in
	  (ops, ids_to_discard, (constl,indl,cstrl))
	else
	  let cb = Environ.lookup_constant sp oldenv in
	  let spid = basename sp in
	  let imp = is_implicit_constant sp in
	  let newsp = recalc_sp dir sp in
	  let mods = 
	    let modl = build_abstract_list cb.const_hyps ids_to_discard in
	    [ (sp, DO_ABSTRACT(newsp,modl)) ]
	  in
	  let r = { d_from = sp;
		    d_modlist = work_alist;
		    d_abstract = ids_to_discard } in
	  let op = Constant (spid,r,stre,imp) in
          (op :: ops, ids_to_discard, (mods@constl, indl, cstrl))
  
    | "INDUCTIVE" ->
	let mib = Environ.lookup_mind sp oldenv in
	let newsp = recalc_sp dir sp in
	let imp = is_implicit_inductive_definition sp in
	let (mie,indmods,cstrmods) = 
	  process_inductive sp newsp oldenv (ids_to_discard,work_alist) mib in
	((Inductive(mie,imp)) :: ops, ids_to_discard,
	 (constl,indmods@indl,cstrmods@cstrl))

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
	let newsp = recalc_sp dir sp in
	let mib = Environ.lookup_mind sp oldenv in
	let strobj =
	  { s_CONST = info.s_CONST;
	    s_PARAM = mib.mind_nparams;
	    s_PROJ = List.map (option_app (recalc_sp dir)) info.s_PROJ } in
	((Struc ((newsp,i),strobj))::ops, ids_to_discard, work_alist)

    (***TODO
    | "OBJDEF1" -> 
	let sp = outObjDef1 lobj in
        let ((_,spid,_)) = repr_path sp in
        begin try objdef_declare spid with _ -> () end;
        (ids_to_discard,work_alist)
    ***)

    | _ -> (ops,ids_to_discard,work_alist)

let process_item oldenv dir sec_sp acc = function
  | (sp,Leaf lobj) -> process_object oldenv dir sec_sp acc (sp,lobj)
  | (_,_) -> acc

let process_operation = function
  | Variable (id,expmod_a,stre,sticky,imp) ->
      (* Warning:parentheses needed to get a side-effect from with_implicits *)
      with_implicits imp (declare_variable id) (expmod_a,stre,sticky)
  | Parameter (spid,typ,imp) ->
      with_implicits imp (declare_parameter spid) typ;
      constant_message spid
  | Constant (spid,r,stre,imp) ->
      with_implicits imp (declare_constant spid) (ConstantRecipe r,stre);
      constant_message spid
  | Inductive (mie,imp) ->
      let _ = with_implicits imp declare_mind mie in
      inductive_message mie.mind_entry_inds
  | Class (y1,y2) ->
      Lib.add_anonymous_leaf (inClass (y1,y2))
  | Struc (newsp,strobj) ->
      Lib.add_anonymous_leaf (inStruc (newsp,strobj))
  | Coercion ((_,_,clt) as y,idf,ps) ->
      Lib.add_anonymous_leaf (inCoercion y) 

let push_inductive_names ccitab sp mie =
  let _,ccitab =
    List.fold_left
      (fun (n,ccitab) (id,_,cnames,_) ->
	 let indsp = (sp,n) in
	 let _,ccitab =
	   List.fold_left
	     (fun (p,ccitab) x ->
		(p+1,Idmap.add x (ConstructRef (indsp,p)) ccitab))
	     (1,Idmap.add id (IndRef indsp) ccitab)
	     cnames in
	 (n+1,ccitab))
      (0,ccitab)
      mie.mind_entry_inds
  in ccitab

let rec process_object (ccitab, objtab, modtab as tabs) = function
  | sp,Leaf obj -> 
      begin match object_tag obj with
	| "CONSTANT" | "PARAMETER" ->
            (Idmap.add (basename sp) (ConstRef sp) ccitab,objtab,modtab)
	| "INDUCTIVE" ->
	    let mie,_ = out_inductive obj in
	    (push_inductive_names ccitab sp mie, objtab, modtab)
        (* Variables are never visible *)
	| "VARIABLE" -> tabs
        (* All the rest is visible only at toplevel ??? *)
        (* Actually it is unsafe, it should be visible only in empty context *)
        (* ou quelque chose comme cela *)
	| "CLASS" | "COERCION" | "STRUCTURE" | "OBJDEF1" | "SYNTAXCONSTANT"
	| _ ->
	    (ccitab, Idmap.add (basename sp) (sp,obj) objtab, modtab)
      end 
  | sp,ClosedSection (export,_,seg,contents) ->
      let id = string_of_id (basename sp) in
      (ccitab, objtab, Stringmap.add id contents modtab)
  | _,(OpenedSection _ | FrozenState _ | Module _) -> 
      anomaly "Should not occur in a closed section"

and module_contents seg =
  let ccitab, objtab, modtab =
    List.fold_left process_object (Idmap.empty, Idmap.empty, Stringmap.empty)
      seg
  in Nametab.Closed (ccitab, objtab, modtab)

let close_section _ s = 
  let oldenv = Global.env() in
  let process_segment sec_sp decls =
    let newdir = dirpath sec_sp in
    let olddir = wd_of_sp sec_sp in
    let (ops,ids,_) = 
      List.fold_left (process_item oldenv newdir olddir) ([],[],([],[],[])) decls in 
    Global.pop_named_decls ids;
    List.iter process_operation (List.rev ops);
    module_contents decls in
  close_section false process_segment s

let save_module_to s f =
  Library.save_module_to module_contents s f

