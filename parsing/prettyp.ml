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
open Term
open Termops
open Declarations
open Inductive
open Inductiveops
open Sign
open Reduction
open Environ
open Instantiate
open Declare
open Impargs
open Libobject
open Printer
open Printmod
open Libnames
open Nametab

let print_basename sp = pr_global (ConstRef sp)

let print_closed_sections = ref false

let print_typed_value_in_env env (trm,typ) =
  (prterm_env env trm ++ fnl () ++
     str "     : " ++ prtype_env env typ ++ fnl ())

let print_typed_value x = print_typed_value_in_env (Global.env ()) x
			  		  
let print_impl_args_by_pos = function
  | []  -> mt ()
  | [i] -> str"Position [" ++ int i ++ str"] is implicit"
  | l   -> 
      str"Positions [" ++ 
      prlist_with_sep (fun () -> str "; ") int l ++
      str"] are implicit"

let print_impl_args l = print_impl_args_by_pos (positions_of_implicits l)

(* To be improved; the type should be used to provide the types in the
   abstractions. This should be done recursively inside prterm, so that
   the pretty-print of a proposition (P:(nat->nat)->Prop)(P [u]u)
   synthesizes the type nat of the abstraction on u *)

let print_named_def name body typ =
  let pbody = prterm body in
  let ptyp = prtype typ in
  (str "*** [" ++ str name ++ str " " ++
     hov 0 (str ":=" ++ brk (1,2) ++ pbody ++ spc () ++
	      str ":" ++ brk (1,2) ++ ptyp) ++
	   str "]" ++ fnl ())

let print_named_assum name typ =
  (str "*** [" ++ str name ++ str " : " ++ prtype typ ++ str "]" ++ fnl ())

let print_named_decl (id,c,typ) =
  let s = string_of_id id in
  match c with
    | Some body -> print_named_def s body typ
    | None -> print_named_assum s typ

let assumptions_for_print lna =
  List.fold_right (fun na env -> add_name na env) lna empty_names_context

let implicit_args_id id l =
  if List.exists is_status_implicit l then 
    (str"For " ++ pr_id id ++ str": " ++ print_impl_args l ++ fnl ())
  else 
    (mt ())

let implicit_args_msg sp mipv = 
  (prvecti
       (fun i mip -> 
	  let imps = inductive_implicits_list (sp,i) in
          ((implicit_args_id mip.mind_typename imps) ++
             prvecti 
	       (fun j idc ->
		  let imps = constructor_implicits_list ((sp,i),succ j) in
                  (implicit_args_id idc imps))
               mip.mind_consnames 
))
       mipv)

let print_params env params =
  if List.length params = 0 then 
    (mt ()) 
  else
    (str "[" ++ pr_rel_context env params ++ str "]" ++ brk(1,2))

let print_constructors envpar names types =
  let pc =
    prvect_with_sep (fun () -> brk(1,0) ++ str "| ")
      (fun (id,c) -> pr_id id ++ str " : " ++ prterm_env envpar c)
      (array_map2 (fun n t -> (n,t)) names types)
  in 
  hv 0 (str "  " ++ pc)

let build_inductive sp tyi =
  let (mib,mip) = Global.lookup_inductive (sp,tyi) in
  let params = mip.mind_params_ctxt in
  let args = extended_rel_list 0 params in
  let env = Global.env() in
  let arity = hnf_prod_applist env mip.mind_user_arity args in
  let cstrtypes = arities_of_constructors env (sp,tyi) in
  let cstrtypes =
    Array.map (fun c -> hnf_prod_applist env c args) cstrtypes in
  let cstrnames = mip.mind_consnames in
  (IndRef (sp,tyi), params, arity, cstrnames, cstrtypes)

let print_one_inductive sp tyi =
  let (ref, params, arity, cstrnames, cstrtypes) = build_inductive sp tyi in
  let env = Global.env () in
  let envpar = push_rel_context params env in
  (hov 0
     ((hov 0
	   (pr_global (IndRef (sp,tyi)) ++ brk(1,2) ++ print_params env params ++
	      str ": " ++ prterm_env envpar arity ++ str " :=")) ++
	brk(1,2) ++ print_constructors envpar cstrnames cstrtypes)) 

let print_mutual sp =
  let (mib,mip) = Global.lookup_inductive (sp,0) in
  let mipv = mib.mind_packets in
  if Array.length mib.mind_packets = 1 then
    let (ref, params, arity, cstrnames, cstrtypes) = build_inductive sp 0 in
    let sfinite =
      if mib.mind_finite then "Inductive " else "CoInductive " in
    let env = Global.env () in
    let envpar = push_rel_context params env in
    (hov 0 (
       str sfinite ++ 
      pr_global (IndRef (sp,0)) ++ brk(1,2) ++
       print_params env params ++ brk(1,5) ++
       str": " ++ prterm_env envpar arity ++ str" :=" ++
       brk(0,4) ++ print_constructors envpar cstrnames cstrtypes ++ fnl () ++
       implicit_args_msg sp mib.mind_packets) )
  (* Mutual [co]inductive definitions *)
  else
    let _,(mipli,miplc) =
      Array.fold_right
        (fun mi (n,(li,lc)) ->
           if mib.mind_finite then (n+1,(n::li,lc)) else (n+1,(li,n::lc)))
        mipv (0,([],[])) 
    in 
    let strind =
      if mipli = [] then (mt ()) 
      else (str "Inductive" ++ brk(1,4) ++
              (prlist_with_sep
                 (fun () -> (fnl () ++ str"  with" ++ brk(1,4)))
                 (print_one_inductive sp) mipli) ++ fnl ())
    and strcoind =
      if miplc = [] then (mt ()) 
      else (str "CoInductive" ++ brk(1,4) ++
              (prlist_with_sep
                 (fun () -> (fnl () ++ str "  with" ++ brk(1,4))) 
                 (print_one_inductive sp) miplc) ++ fnl ()) 
    in
    (hv 0 (str"Mutual " ++
           (if mib.mind_finite then 
	      strind ++ strcoind
            else 
	      strcoind ++ strind) ++
           implicit_args_msg sp mipv))

(*
  let env = Global.env () in
  let evd = Evd.empty in
  let {mind_packets=mipv} = mib in 
  (* On suppose que tous les inductifs ont les même paramètres *)
  let nparams = mipv.(0).mind_nparams in
  let (lpars,_) = decomp_n_prod env evd nparams
		    (body_of_type (mind_user_arity mipv.(0))) in
  let arities = Array.map (fun mip -> (Name mip.mind_typename, None, mip.mind_nf_arity)) mipv in
  let env_ar = push_rels lpars env in
  let pr_constructor (id,c) =
    (pr_id id ++ str " : " ++ prterm_env env_ar c) in
  let print_constructors mis =
    let (_,lC) = mis_type_mconstructs mis in
    let lidC =
      array_map2 (fun id c -> (id, snd (decomp_n_prod env evd nparams c)))
	(mis_consnames mis) lC in
    let plidC =
      prvect_with_sep (fun () -> (brk(0,0) ++ str "| "))
        pr_constructor
	lidC
    in
    hV 0 (str "  " ++ plidC) 
  in
  let params =
    if nparams = 0 then 
      (mt ()) 
    else
      (str "[" ++ pr_rel_context env lpars ++ str "]" ++ brk(1,2)) in
  let print_oneind tyi =
    let mis =
      build_mis
	((sp,tyi),
	 Array.of_list (instance_from_section_context mib.mind_hyps))
	mib in
    let (_,arity) = decomp_n_prod env evd nparams
		      (body_of_type (mis_user_arity mis)) in
      (hov 0
         ((hov 0
	       (pr_global (IndRef (sp,tyi)) ++ brk(1,2) ++ params ++
	          str ": " ++ prterm_env env_ar arity ++ str " :=")) ++
            brk(1,2) ++ print_constructors mis)) 
  in 
  let mis0 =
    build_mis
      ((sp,0),Array.of_list (instance_from_section_context mib.mind_hyps))
      mib in
  (* Case one [co]inductive *)
  if Array.length mipv = 1 then
    let (_,arity) = decomp_n_prod env evd nparams
		      (body_of_type (mis_user_arity mis0)) in 
    let sfinite = if mis_finite mis0 then "Inductive " else "CoInductive " in
    (hov 0 (str sfinite ++ pr_global (IndRef (sp,0)) ++
              if nparams = 0 then 
		(mt ()) 
              else 
		(str" [" ++ pr_rel_context env lpars ++ str "]") ++
              brk(1,5) ++ str": " ++ prterm_env env_ar arity ++ str" :=" ++
              brk(0,4) ++ print_constructors mis0 ++ fnl () ++
              implicit_args_msg sp mipv) )
  (* Mutual [co]inductive definitions *)
  else
    let _,(mipli,miplc) =
      List.fold_left 
        (fun (n,(li,lc)) mi ->
           if mi.mind_finite then (n+1,(n::li,lc)) else (n+1,(li,n::lc)))
        (0,([],[])) (Array.to_list mipv) 
    in 
    let strind =
      if mipli = [] then (mt ()) 
      else (str "Inductive" ++ brk(1,4) ++
              (prlist_with_sep
                 (fun () -> (fnl () ++ str"  with" ++ brk(1,4)))
                 print_oneind
                 (List.rev mipli)) ++ fnl ())
    and strcoind =
      if miplc = [] then (mt ()) 
      else (str "CoInductive" ++ brk(1,4) ++
              (prlist_with_sep
                 (fun () -> (fnl () ++ str "  with" ++ brk(1,4))) 
                 print_oneind (List.rev miplc)) ++ fnl ()) 
    in
    (hV 0 (str"Mutual " ++ 
             if mis_finite mis0 then 
	       (strind ++ strcoind) 
             else 
	       (strcoind ++ strind) ++
             implicit_args_msg sp mipv))
*)
let print_section_variable sp =
  let d = get_variable sp in
  let l = implicits_of_var sp in
  (print_named_decl d ++ print_impl_args l)

let print_body = function
  | Some lc  -> prterm (Declarations.force lc)
  | None -> (str"<no body>")

let print_typed_body (val_0,typ) =
  (print_body val_0 ++ fnl () ++ str "     : " ++ prtype typ ++ fnl ())

let print_constant with_values sep sp =
  let cb = Global.lookup_constant sp in
  let val_0 = cb.const_body in
  let typ = cb.const_type in
  let impls = constant_implicits_list sp in
  hov 0 ((match val_0 with 
		| None -> 
		    (str"*** [ " ++ 
		       print_basename sp ++  
		       str " : " ++ cut () ++ prtype typ ++ str" ]" ++ fnl ())
		| _ -> 
		    (print_basename sp ++ 
		       str sep ++ cut () ++
		       if with_values then 
			 print_typed_body (val_0,typ) 
		       else 
			 (prtype typ ++ fnl ()))) ++ 
	     print_impl_args impls)

let print_inductive sp = (print_mutual sp)

let print_syntactic_def sep kn =
  let l = label kn in
  let c = Syntax_def.search_syntactic_definition dummy_loc kn in 
  (str" Syntactic Definition " ++ pr_lab l ++ str sep ++ 
  Constrextern.without_symbols pr_rawterm c ++ fnl ())

(*let print_module with_values kn = 
  str "Module " ++ pr_id (id_of_label (label kn)) ++ fnl () ++ fnl ()

let print_modtype kn =
  str "Module Type " ++ pr_id (id_of_label (label kn)) ++ fnl () ++ fnl ()
*)

let print_leaf_entry with_values sep ((sp,kn as oname),lobj) =
  let tag = object_tag lobj in
  match (oname,tag) with
    | (_,"VARIABLE") ->
	print_section_variable (basename sp) ++ fnl ()
    | (_,"CONSTANT") ->
	print_constant with_values sep kn ++ fnl ()
    | (_,"INDUCTIVE") ->
	print_inductive kn ++ fnl ()
    | (_,"MODULE") ->
	let (mp,_,l) = repr_kn kn in 
	  print_module with_values (MPdot (mp,l)) ++ fnl ()
    | (_,"MODULE TYPE") ->
	print_modtype kn ++ fnl ()
    | (_,"AUTOHINT") -> 
(*	(str" Hint Marker" ++ fnl ())*)
	(mt ())
    | (_,"GRAMMAR") -> 
(*	(str" Grammar Marker" ++ fnl ())*)
	(mt ())
    | (_,"SYNTAXCONSTANT") -> 
	print_syntactic_def sep kn ++ fnl ()
    | (_,"PPSYNTAX") -> 
(*	(str" Syntax Marker" ++ fnl ())*)
	(mt ())
    | (_,"TOKEN") -> 
(*	(str" Token Marker" ++ fnl ())*)
	(mt ())
    | (_,"CLASS") -> 
(*	(str" Class Marker" ++ fnl ())*)
	(mt ())
    | (_,"COERCION") -> 
(*	(str" Coercion Marker" ++ fnl ())*)
	(mt ())
    | (_,"REQUIRE") -> 
(*	(str" Require Marker" ++ fnl ())*)
	(mt ())
    | (_,"END-SECTION") -> (mt ())
    | (_,"STRUCTURE") -> (mt ())
(* To deal with forgotten cases... *)
    | (_,s) -> (mt ())
(*
    | (_,s) -> 
	(str(string_of_path sp) ++ str" : " ++
           str"Unrecognized object " ++ str s ++ fnl ())
*)

let rec print_library_entry with_values ent = 
  let sep = if with_values then " = " else " : " in 
  let pr_name (sp,_) = pr_id (basename sp) in
  match ent with
    | (oname,Lib.Leaf lobj) -> 
	(print_leaf_entry with_values sep (oname,lobj))
    | (oname,Lib.OpenedSection (dir,_)) -> 
        (str " >>>>>>> Section " ++ pr_name oname ++ fnl ())
    | (oname,Lib.ClosedSection _) -> 
        (str " >>>>>>> Closed Section " ++ pr_name oname ++ fnl ())
    | (_,Lib.CompilingLibrary (dir,_)) ->
	(str " >>>>>>> Library " ++ pr_dirpath dir ++ fnl ())
    | (oname,Lib.OpenedModule _) ->
	(str " >>>>>>> Module " ++ pr_name oname ++ fnl ())
    | (oname,Lib.OpenedModtype _) ->
	(str " >>>>>>> Module Type " ++ pr_name oname ++ fnl ())
    | (_,Lib.FrozenState _) ->
	(mt ())
	
and print_context with_values = 
  let rec prec = function
    | h::rest -> (prec rest ++ print_library_entry with_values h)
    | [] -> (mt ())
  in 
  prec

let print_full_context () = print_context true (Lib.contents_after None)

let print_full_context_typ () = print_context false (Lib.contents_after None)

(* For printing an inductive definition with
   its constructors and elimination,
   assume that the declaration of constructors and eliminations
   follows the definition of the inductive type *)

let list_filter_vec f vec = 
  let rec frec n lf = 
    if n < 0 then lf 
    else if f vec.(n) then 
      frec (n-1) (vec.(n)::lf)
    else 
      frec (n-1) lf
  in 
  frec (Array.length vec -1) []

(* This is designed to print the contents of an opened section *)
let read_sec_context r =
  let loc,qid = qualid_of_reference r in
  let dir =
    try Nametab.locate_section qid
    with Not_found ->
      user_err_loc (loc,"read_sec_context", str "Unknown section") in
  let rec get_cxt in_cxt = function
    | ((_,Lib.OpenedSection ((dir',_),_)) as hd)::rest ->
        if dir = dir' then (hd::in_cxt) else get_cxt (hd::in_cxt) rest
    | ((_,Lib.ClosedSection (_,_,ctxt)) as hd)::rest ->
        error "Cannot print the contents of a closed section"
    | [] -> []
    | hd::rest -> get_cxt (hd::in_cxt) rest 
  in
  let cxt = (Lib.contents_after None) in
  List.rev (get_cxt [] cxt)

let print_sec_context sec = print_context true (read_sec_context sec)

let print_sec_context_typ sec = print_context false (read_sec_context sec)

let print_judgment env {uj_val=trm;uj_type=typ} =
  print_typed_value_in_env env (trm, typ)
    
let print_safe_judgment env j =
  let trm = Safe_typing.j_val j in
  let typ = Safe_typing.j_type j in
  print_typed_value_in_env env (trm, typ)
    
let print_eval red_fun env {uj_val=trm;uj_type=typ} =
  let ntrm = red_fun env Evd.empty trm in
  (str "     = " ++ print_judgment env {uj_val = ntrm; uj_type = typ})

let print_name r = 
  let loc,qid = qualid_of_reference r in
  try 
    let sp = Nametab.locate_obj qid in
    let (oname,lobj) = 
      let (oname,entry) =
	List.find (fun en -> (fst (fst en)) = sp) (Lib.contents_after None)
      in
      match entry with
	| Lib.Leaf obj -> (oname,obj)
	| _ -> raise Not_found
    in
    print_leaf_entry true " = " (oname,lobj)
  with Not_found -> 
  try 
    match Nametab.locate qid with
      | ConstRef sp -> print_constant true " = " sp
      | IndRef (sp,_) -> print_inductive sp
      | ConstructRef ((sp,_),_) -> print_inductive sp
      | VarRef sp -> print_section_variable sp
  with Not_found -> 
  try  (* Var locale de but, pas var de section... donc pas d'implicits *)
    let dir,str = repr_qualid qid in 
    if (repr_dirpath dir) <> [] then raise Not_found;
    let (_,c,typ) = Global.lookup_named str in 
    (print_named_decl (str,c,typ))
  with Not_found ->
  try
    let kn = Nametab.locate_syntactic_definition qid in
    print_syntactic_def " = " kn
  with Not_found ->
  try print_module true (Nametab.locate_module qid)
  with Not_found -> 
  try print_modtype (Nametab.locate_modtype qid)
  with Not_found ->
    user_err_loc
      (loc,"print_name",pr_qualid qid ++ spc () ++ str "not a defined object")

let print_opaque_name qid = 
  let sigma = Evd.empty in
  let env = Global.env () in
  let sign = Global.named_context () in
  match global qid with
    | ConstRef cst ->
	let cb = Global.lookup_constant cst in
        if cb.const_body <> None then
	  print_constant true " = " cst
        else 
	  error "not a defined constant"
    | IndRef (sp,_) ->
        print_mutual sp
    | ConstructRef cstr -> 
	let ty = Inductive.type_of_constructor env cstr in
	print_typed_value (mkConstruct cstr, ty)
    | VarRef id ->
        let (_,c,ty) = lookup_named id env in 
	print_named_decl (id,c,ty)

let print_local_context () =
  let env = Lib.contents_after None in
  let rec print_var_rec = function 
    | [] -> (mt ())
    | (oname,Lib.Leaf lobj)::rest ->
	if "VARIABLE" = object_tag lobj then
          let d = get_variable (basename (fst oname)) in 
	  (print_var_rec rest ++
             print_named_decl d)
	else 
	  print_var_rec rest
    | _::rest -> print_var_rec rest

  and print_last_const = function
    | (oname,Lib.Leaf lobj)::rest -> 
        (match object_tag lobj with
           | "CONSTANT" -> 
	       let kn = snd oname in
               let {const_body=val_0;const_type=typ} = 
		 Global.lookup_constant kn in
		 (print_last_const rest ++
                  print_basename kn ++str" = " ++
                  print_typed_body (val_0,typ))
           | "INDUCTIVE" -> 
	       let kn = snd oname in
               (print_last_const rest ++print_mutual kn ++ fnl ())
           | "VARIABLE" ->  (mt ())
           | _          ->  print_last_const rest)
    | _ -> (mt ())
  in 
  (print_var_rec env ++  print_last_const env)

let fprint_var name typ =
  (str ("*** [" ^ name ^ " :") ++ fprtype typ ++ str "]" ++ fnl ())

let fprint_judge {uj_val=trm;uj_type=typ} = 
  (fprterm trm ++ str" : " ++ fprterm typ)

let unfold_head_fconst = 
  let rec unfrec k = match kind_of_term k with
    | Const cst -> constant_value (Global.env ()) cst 
    | Lambda (na,t,b) -> mkLambda (na,t,unfrec b)
    | App (f,v) -> appvect (unfrec f,v)
    | _ -> k
  in 
  unfrec

(* for debug *)
let inspect depth = 
  let rec inspectrec n res env = 
    if n=0 or env=[] then 
      res
    else 
      inspectrec (n-1) (List.hd env::res) (List.tl env)
  in 
  let items = List.rev (inspectrec depth [] (Lib.contents_after None)) in
  print_context false items


(*************************************************************************)
(* Pretty-printing functions coming from classops.ml                     *)

open Classops

let print_coercion_value v = prterm (get_coercion_value v)

let print_index_coercion c = 
  let _,v = coercion_info_from_index c in
  print_coercion_value v

let print_class i =
  let cl,_ = class_info_from_index i in
  (str (string_of_class cl))
  
let print_path ((i,j),p) = 
  (str"[" ++ 
     prlist_with_sep (fun () -> (str"; "))
       (fun c ->  print_index_coercion c) p ++
     str"] : " ++ print_class i ++ str" >-> " ++
     print_class j)

let _ = Classops.install_path_printer print_path

let print_graph () = 
  (prlist_with_sep pr_fnl print_path (inheritance_graph()))

let print_classes () = 
  (prlist_with_sep pr_spc
       (fun (_,(cl,x)) -> 
          (str (string_of_class cl)
	       (* ++ str(string_of_strength x.cl_strength) *))) 
       (classes()))

let print_coercions () = 
  (prlist_with_sep pr_spc
       (fun (_,(_,v)) -> (print_coercion_value v)) (coercions()))
  
let index_of_class cl =
  try 
    fst (class_info cl)
  with _ -> 
    errorlabstrm "index_of_class"
      (str(string_of_class cl) ++ str" is not a defined class")

let print_path_between cls clt = 
  let i = index_of_class cls in
  let j = index_of_class clt in
  let p = 
    try 
      lookup_path_between (i,j) 
    with _ -> 
      errorlabstrm "index_cl_of_id"
        (str"No path between " ++str(string_of_class cls) ++ 
	   str" and " ++str(string_of_class clt))
  in
  print_path ((i,j),p)

(*************************************************************************)
