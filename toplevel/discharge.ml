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
open Names
open Nameops
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
open Indtypes
open Nametab

let recalc_sp dir sp =
  let (_,spid) = repr_path sp in Libnames.make_path dir spid

let recalc_kn dir kn = 
  let (mp,_,l) = Names.repr_kn kn in
    Names.make_kn mp dir l

let rec find_var id = function
  | [] -> false
  | (x,b,_)::l -> if x = id then b=None else find_var id l

let build_abstract_list hyps ids_to_discard =
  let l =
    List.fold_left
      (fun vars id -> if find_var id hyps then mkVar id::vars else vars)
      [] ids_to_discard in
  Array.of_list l

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
    inds' in
  let abstract_one_def id c inds =
    List.map
      (function (np,tname,arity,cnames,lc) -> 
	 let arity' = replace_vars [id, c] arity in
	 let lc' = List.map (replace_vars [id, c]) lc in
         (np,tname,arity',cnames,lc'))
      inds in
  let abstract_once ((hyps,inds,vars) as sofar) id =
    match hyps with
      | (hyp,None,t as d)::rest when id = hyp ->
	  let inds' = abstract_one_assum hyp t inds in 
	  (rest, inds', mkVar id::vars)
      | (hyp,Some b,t as d)::rest when id = hyp ->
	  let inds' = abstract_one_def hyp b inds in 
	  (rest, inds', vars)
      | _ -> sofar in
  let (_,inds',vars) =
    List.fold_left abstract_once (hyps,inds,[]) ids_to_abs in
  let inds'' =
    List.map 
      (fun (nparams,a,arity,c,lc) ->
	 let nparams' = nparams + (List.length vars) in
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
	 { mind_entry_params = params';
	   mind_entry_typename = a;
	   mind_entry_arity = short_arity;
	   mind_entry_consnames = c;
	   mind_entry_lc = shortlc })
      inds' in
  (inds'', Array.of_list vars)

let process_inductive osecsp nsecsp oldenv (ids_to_discard,modlist) mib =
  assert (Array.length mib.mind_packets > 0);
  let finite = mib.mind_finite in
  let inds = 
    array_map_to_list
      (fun mip ->
	 let nparams = mip.mind_nparams in
	 let arity = expmod_type modlist mip.mind_user_arity in
	 let lc = Array.map (expmod_type modlist) mip.mind_user_lc in
	 (nparams,
	  mip.mind_typename,
	  arity,
	  Array.to_list mip.mind_consnames,
	  Array.to_list lc))
      mib.mind_packets
  in
  let hyps = mib.mind_hyps in
  let hyps' =
    Sign.fold_named_context
      (fun (x,b,t) sgn ->
        Sign.add_named_decl
          (x, option_app (expmod_constr modlist) b,expmod_constr modlist t)
          sgn)
      mib.mind_hyps ~init:empty_named_context in
  let (inds',abs_vars) = abstract_inductive ids_to_discard hyps' inds in
  let lmodif_one_mind i = 
    let nbc = Array.length mib.mind_packets.(i).mind_consnames in 
    (((osecsp,i), DO_ABSTRACT ((nsecsp,i),abs_vars)),
     list_tabulate
       (function j -> 
	  let j' = j + 1 in
	  (((osecsp,i),j'), DO_ABSTRACT (((nsecsp,i),j'),abs_vars)))
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
  Options.if_verbose ppnl (pr_id id ++ str " is discharged.")

let inductive_message inds =
  Options.if_verbose 
    ppnl
      (hov 0 
	 (match inds with
	    | [] -> assert false
	    | [ind] ->
		(pr_id ind.mind_entry_typename ++ str " is discharged.")
	    | l ->
		(prlist_with_sep pr_coma 
		     (fun ind -> pr_id ind.mind_entry_typename) l ++
		   spc () ++ str "are discharged.")))

(* Discharge operations for the various objects of the environment. *)

type opacity = bool

type discharge_operation = 
  | Variable of identifier * section_variable_entry * strength * bool
  | Constant of identifier * recipe * strength * constant * bool
  | Inductive of mutual_inductive_entry * bool
  | Class of cl_typ * cl_info_typ
  | Struc of inductive * (unit -> struc_typ)
  | Objdef of constant
  | Coercion of coercion_entry
  | Require of module_reference
  | Constraints of Univ.constraints

(* Main function to traverse the library segment and compute the various
   discharge operations. *)

let process_object oldenv dir sec_sp
  (ops,ids_to_discard,(constl,indl,cstrl as work_alist)) (sp,lobj) =
  let tag = object_tag lobj in 
  match tag with
    | "VARIABLE" ->
	let ((id,c,t),cst,stre) =
          get_variable_with_constraints (basename sp) in
	(* VARIABLE means local (entry Variable/Hypothesis/Local and are *)
	(* always discharged *)
(*
 	if stre = (DischargeAt sec_sp) or ids_to_discard <> [] then
*)
	  (Constraints cst :: ops, id :: ids_to_discard, work_alist)
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

    | ("CONSTANT" | "PARAMETER") ->
	(* CONSTANT/PARAMETER means never discharge (though visibility *)
	(* may vary) *)
 	let stre = constant_strength sp in
(*
	if stre = (DischargeAt sec_sp) then
	  let cb = Environ.lookup_constant sp oldenv in
	  let constl = (sp, DO_REPLACE cb)::constl in
	  (ops, ids_to_discard, (constl,indl,cstrl))
	else
*)
	let kn = Nametab.locate_constant (qualid_of_sp sp) in
	let lab = label kn in
	let cb = Environ.lookup_constant kn oldenv in
	let imp = is_implicit_constant kn in
	let newkn = match stre with
	  | DischargeAt (d,_) when not (is_dirpath_prefix_of d dir) -> kn
	  | _ -> recalc_kn dir kn in
        let mods = 
	  let abs_vars = build_abstract_list cb.const_hyps ids_to_discard in
	  [ (kn, DO_ABSTRACT(newkn,abs_vars)) ]
	in
	let r = { d_from = cb;
	          d_modlist = work_alist;
	          d_abstract = ids_to_discard } in
	let op = Constant (id_of_label lab, r,stre,newkn,imp) in
        (op :: ops, ids_to_discard, (mods@constl, indl, cstrl))
  
    | "INDUCTIVE" ->
	let kn = Nametab.locate_mind (qualid_of_sp sp) in
	let mib = Environ.lookup_mind kn oldenv in
	let newkn = recalc_kn dir kn in
	let imp = is_implicit_args() (* CHANGE *) in
	let (mie,indmods,cstrmods) = 
	  process_inductive kn newkn oldenv (ids_to_discard,work_alist) mib in
	((Inductive(mie,imp)) :: ops, ids_to_discard,
	 (constl,indmods@indl,cstrmods@cstrl))

    | "CLASS" -> 
	let ((cl,clinfo) as x) = outClass lobj in
	if (match clinfo.cl_strength with DischargeAt (sp,_) -> sp = sec_sp | _ -> false) then 
	  (ops,ids_to_discard,work_alist)
	else
	  let (y1,y2) = process_class sec_sp ids_to_discard x in
          ((Class (y1,y2))::ops, ids_to_discard, work_alist)
	  
    | "COERCION" -> 
	let (((_,coeinfo),_,_)as x) = outCoercion lobj in
	if (match coercion_strength coeinfo with DischargeAt (sp,_) -> sp = sec_sp | _ -> false) then 
	  (ops,ids_to_discard,work_alist)
        else
	  let y = process_coercion sec_sp ids_to_discard x in
          ((Coercion y)::ops, ids_to_discard, work_alist)
                    
    | "STRUCTURE" ->
	let ((kn,i),info) = outStruc lobj in
	let newkn = recalc_kn dir kn in
	let strobj () =
	  let mib = Environ.lookup_mind newkn (Global.env ()) in
	  { s_CONST = info.s_CONST;
	    s_PARAM = mib.mind_packets.(0).mind_nparams;
	    s_PROJ = List.map (option_app (fun kn -> Global.get_kn dir (label kn))) info.s_PROJ } in
	((Struc ((newkn,i),strobj))::ops, ids_to_discard, work_alist)

    | "OBJDEF1" -> 
	let kn = outObjDef1 lobj in
	let new_kn = recalc_kn dir kn in
        ((Objdef new_kn)::ops, ids_to_discard, work_alist)

    | "REQUIRE" -> 
	let c = out_require lobj in
	((Require c)::ops, ids_to_discard, work_alist)

    | _ -> (ops,ids_to_discard,work_alist)

let process_item oldenv dir sec_sp acc = function
  | (sp,Leaf lobj) -> process_object oldenv dir sec_sp acc (sp,lobj)
  | (_,_) -> acc

let process_operation = function
  | Variable (id,expmod_a,stre,imp) ->
      (* Warning:parentheses needed to get a side-effect from with_implicits *)
      let _ =
        with_implicits imp (declare_variable id) (Lib.cwd(),expmod_a,stre) in
      ()
  | Constant (id,r,stre,kn,imp) ->
      with_implicits imp (redeclare_constant id) (r,stre,kn);
      constant_message id
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
  | Constraints y -> Global.add_constraints y

let catch_not_found f x =
  try f x
  with Not_found ->
    error ("Something is missing; perhaps a reference to a"^
    " module required inside the section")

let close_section _ s = 
  let oldenv = Global.env() in
  let full_olddir,olddir,decls,fs = close_section false s in
  let newdir = fst (split_dirpath olddir) in
  let (ops,ids,_) = 
    List.fold_left 
      (process_item oldenv newdir olddir) ([],[],([],[],[])) decls 
  in
  let ids = last_section_hyps olddir in
  Summary.unfreeze_lost_summaries fs;
  catch_not_found (List.iter process_operation) (List.rev ops);
  Nametab.push_section full_olddir

