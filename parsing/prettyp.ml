(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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

(*********************)
(** Basic printing   *)

let print_basename sp = pr_global (ConstRef sp)

let print_closed_sections = ref false

(********************************)
(** Printing implicit arguments *)
			  		  
let print_impl_args_by_pos = function
  | []  -> mt ()
  | [i] -> str"Position [" ++ int i ++ str"] is implicit" ++ fnl()
  | l   -> 
      str"Positions [" ++ 
      prlist_with_sep (fun () -> str "; ") int l ++
      str"] are implicit" ++ fnl()

let print_impl_args_by_name = function
  | []  -> mt ()
  | [i] -> str"Argument " ++ pr_id (name_of_implicit i) ++ str" is implicit" ++
      fnl()
  | l   -> 
      str"Arguments " ++ 
      prlist_with_sep (fun () -> str ", ")
        (fun imp -> pr_id (name_of_implicit imp)) l ++
      str" are implicit" ++ fnl()

let print_impl_args l = 
  if !Options.v7 then print_impl_args_by_pos (positions_of_implicits l)
  else print_impl_args_by_name (List.filter is_status_implicit l)

(*********************)
(** Printing Scopes  *)

let print_ref reduce ref =
  let typ = Global.type_of_global ref in
  let typ = 
    if reduce then
      let ctx,ccl = Reductionops.splay_prod_assum (Global.env()) Evd.empty typ
      in it_mkProd_or_LetIn ccl ctx 
    else typ in
  hov 0 (pr_global ref ++ str " :" ++ spc () ++ prtype typ) ++ fnl ()

let print_argument_scopes = function
  | [Some sc] -> str"Argument scope is [" ++ str sc ++ str"]" ++ fnl()
  | l when not (List.for_all ((=) None) l) ->
      hov 2 (str"Argument scopes are" ++ spc() ++ 
      str "[" ++ 
      prlist_with_sep spc (function Some sc -> str sc | None -> str "_") l ++
      str "]") ++ fnl()
  | _  -> mt()

let need_expansion impl ref = 
  let typ = Global.type_of_global ref in
  let ctx = fst (decompose_prod_assum typ) in
  let nprods = List.length (List.filter (fun (_,b,_) -> b=None) ctx) in
  impl <> [] & let _,lastimpl = list_chop nprods impl in
  List.filter is_status_implicit lastimpl <> []

let print_name_infos ref =
  let impl = implicits_of_global ref in
  let scopes = Symbols.find_arguments_scope ref in
  let type_for_implicit = 
    if need_expansion impl ref then
      (* Need to reduce since implicits are computed with products flattened *)
      str "Expanded type for implicit arguments" ++ fnl () ++ 
      print_ref true ref ++ fnl()
    else mt() in
  (if (List.filter is_status_implicit impl<>[])
      or not (List.for_all ((=) None) scopes) 
  then fnl()
  else mt())
  ++ type_for_implicit 
  ++ print_impl_args impl ++ print_argument_scopes scopes

let print_id_args_data test pr id l =
  if List.exists test l then
    str"For " ++ pr_id id ++ str": " ++ pr l
  else 
    mt()

let print_args_data_of_inductive_ids get test pr sp mipv =
  prvecti
    (fun i mip -> 
      print_id_args_data test pr mip.mind_typename (get (IndRef (sp,i))) ++
      prvecti 
	(fun j idc ->
	  print_id_args_data test pr idc (get (ConstructRef ((sp,i),j+1))))
        mip.mind_consnames)
    mipv

let print_inductive_implicit_args =
  print_args_data_of_inductive_ids
    implicits_of_global is_status_implicit print_impl_args

let print_inductive_argument_scopes =
  print_args_data_of_inductive_ids 
    Symbols.find_arguments_scope ((<>) None) print_argument_scopes

(*********************)
(* "Locate" commands *)

type logical_name =
  | Term of global_reference
  | Dir of global_dir_reference
  | Syntactic of kernel_name
  | ModuleType of qualid * kernel_name
  | Undefined of qualid

let locate_any_name ref =
  let module N = Nametab in
  let (loc,qid) = qualid_of_reference ref in
  try Term (N.locate qid)
  with Not_found -> 
  try Syntactic (N.locate_syntactic_definition qid)
  with Not_found ->
  try Dir (N.locate_dir qid)
  with Not_found ->
  try ModuleType (qid, N.locate_modtype qid)
  with Not_found -> Undefined qid

let pr_located_qualid = function
  | Term ref ->
      let ref_str = match ref with
	  ConstRef _ -> "Constant"
	| IndRef _ -> "Inductive"
	| ConstructRef _ -> "Constructor"
	| VarRef _ -> "Variable" in
      str ref_str ++ spc () ++ pr_sp (Nametab.sp_of_global ref)
  | Syntactic kn ->
      str (if !Options.v7 then "Syntactic Definition" else "Notation") ++ 
      spc () ++ pr_sp (Nametab.sp_of_syntactic_definition kn)
  | Dir dir ->
      let s,dir = match dir with
	| DirOpenModule (dir,_) -> "Open Module", dir
	| DirOpenModtype (dir,_) -> "Open Module Type", dir
	| DirOpenSection (dir,_) -> "Open Section", dir
	| DirModule (dir,_) -> "Module", dir
	| DirClosedSection dir -> "Closed Section", dir
      in
      str s ++ spc () ++ pr_dirpath dir
  | ModuleType (qid,_) ->
      str "Module Type" ++ spc () ++ pr_sp (Nametab.full_name_modtype qid)
  | Undefined qid ->    
      pr_qualid qid ++ str " is not a defined object"

let print_located_qualid ref =
  let (loc,qid) = qualid_of_reference ref in
  let module N = Nametab in
  let expand = function
    | TrueGlobal ref -> 
	Term ref, N.shortest_qualid_of_global Idset.empty ref
    | SyntacticDef kn -> 
	Syntactic kn, N.shortest_qualid_of_syndef Idset.empty kn in
  match List.map expand (N.extended_locate_all qid) with
    | [] -> 
	let (dir,id) = repr_qualid qid in
	if dir = empty_dirpath then
	  str "No object of basename " ++ pr_id id
	else
	  str "No object of suffix " ++ pr_qualid qid
    | l ->
	prlist_with_sep fnl
	(fun (o,oqid) ->
	  hov 2 (pr_located_qualid o ++
	  (if oqid <> qid then
	    spc() ++ str "(visible as " ++ pr_qualid oqid ++ str")"
	  else
	    mt ()))) l

(******************************************)
(**** Printing declarations and judgments *)

let print_typed_value_in_env env (trm,typ) =
  (prterm_env env trm ++ fnl () ++
     str "     : " ++ prtype_env env typ ++ fnl ())

let print_typed_value x = print_typed_value_in_env (Global.env ()) x

let print_judgment env {uj_val=trm;uj_type=typ} =
  print_typed_value_in_env env (trm, typ)
    
let print_safe_judgment env j =
  let trm = Safe_typing.j_val j in
  let typ = Safe_typing.j_type j in
  print_typed_value_in_env env (trm, typ)
    
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

(*********************)
(* *)

let print_params env params =
  if List.length params = 0 then 
    (mt ()) 
  else
    if !Options.v7 then
      (str "[" ++ pr_rel_context env params ++ str "]" ++ brk(1,2))
    else 
      (pr_rel_context env params ++ brk(1,2))

let print_constructors envpar names types =
  let pc =
    prlist_with_sep (fun () -> brk(1,0) ++ str "| ")
      (fun (id,c) -> pr_id id ++ str " : " ++ prterm_env envpar c)
      (Array.to_list (array_map2 (fun n t -> (n,t)) names types))
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

let print_one_inductive (sp,tyi) =
  let (ref, params, arity, cstrnames, cstrtypes) = build_inductive sp tyi in
  let env = Global.env () in
  let envpar = push_rel_context params env in
  hov 0 (
    pr_global (IndRef (sp,tyi)) ++ brk(1,4) ++ print_params env params ++
    str ": " ++ prterm_env envpar arity ++ str " :=") ++
  brk(0,2) ++ print_constructors envpar cstrnames cstrtypes

let pr_mutual_inductive finite indl =
  hov 0 (
    str (if finite then "Inductive " else "CoInductive ") ++
    prlist_with_sep (fun () -> fnl () ++ str"  with ")
      print_one_inductive indl) ++
  fnl ()

let print_mutual sp =
  let (mib,mip) = Global.lookup_inductive (sp,0) in
  let mipv = mib.mind_packets in
  let names = list_tabulate (fun x -> (sp,x)) (Array.length mipv) in
  pr_mutual_inductive mib.mind_finite names ++
  print_inductive_implicit_args sp mipv ++
  print_inductive_argument_scopes sp mipv

let print_section_variable sp =
  let d = get_variable sp in
  print_named_decl d ++ 
  print_name_infos (VarRef sp)

let print_body = function
  | Some lc  -> prterm (Declarations.force lc)
  | None -> (str"<no body>")

let print_typed_body (val_0,typ) =
  (print_body val_0 ++ fnl () ++ str "     : " ++ prtype typ ++ fnl ())

let print_constant with_values sep sp =
  let cb = Global.lookup_constant sp in
  let val_0 = cb.const_body in
  let typ = cb.const_type in
  hov 0 (
    match val_0 with 
    | None -> 
	str"*** [ " ++ 
	print_basename sp ++ str " : " ++ cut () ++ prtype typ ++ 
	str" ]" ++ fnl ()
    | _ -> 
	print_basename sp ++ str sep ++ cut () ++
	(if with_values then print_typed_body (val_0,typ) else prtype typ) ++
	fnl ())

let print_constant_with_infos sp =
  print_constant true " = " sp ++ print_name_infos (ConstRef sp)

let print_inductive sp = (print_mutual sp)

let print_syntactic_def sep kn =
  let qid = Nametab.shortest_qualid_of_syndef Idset.empty kn in
  let c = Syntax_def.search_syntactic_definition dummy_loc kn in 
  (str (if !Options.v7 then "Syntactic Definition " else "Notation ")
   ++ pr_qualid qid ++ str sep ++ 
  Constrextern.without_symbols pr_rawterm c ++ fnl ())

let print_leaf_entry with_values sep ((sp,kn as oname),lobj) =
  let tag = object_tag lobj in
  match (oname,tag) with
    | (_,"VARIABLE") ->
	Some (print_section_variable (basename sp))
    | (_,"CONSTANT") ->
	Some (print_constant with_values sep kn)
    | (_,"INDUCTIVE") ->
	Some (print_inductive kn)
    | (_,"MODULE") ->
	let (mp,_,l) = repr_kn kn in 
	Some (print_module with_values (MPdot (mp,l)))
    | (_,"MODULE TYPE") ->
	Some (print_modtype kn)
    | (_,("AUTOHINT"|"GRAMMAR"|"SYNTAXCONSTANT"|"PPSYNTAX"|"TOKEN"|"CLASS"|
	"COERCION"|"REQUIRE"|"END-SECTION"|"STRUCTURE")) -> None
    (* To deal with forgotten cases... *)
    | (_,s) -> None
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
	print_leaf_entry with_values sep (oname,lobj)
    | (oname,Lib.OpenedSection (dir,_)) -> 
        Some (str " >>>>>>> Section " ++ pr_name oname)
    | (oname,Lib.ClosedSection _) -> 
        Some (str " >>>>>>> Closed Section " ++ pr_name oname)
    | (_,Lib.CompilingLibrary (dir,_)) ->
	Some (str " >>>>>>> Library " ++ pr_dirpath dir)
    | (oname,Lib.OpenedModule _) ->
	Some (str " >>>>>>> Module " ++ pr_name oname)
    | (oname,Lib.OpenedModtype _) ->
	Some (str " >>>>>>> Module Type " ++ pr_name oname)
    | (_,Lib.FrozenState _) ->
	None
	
let print_context with_values = 
  let rec prec n = function
    | h::rest when n = None or out_some n > 0 -> 
	(match print_library_entry with_values h with
	  | None -> prec n rest
	  | Some pp -> prec (option_app ((+) (-1)) n) rest ++ pp ++ fnl ())
    | _ -> mt ()
  in 
  prec

let print_full_context () = 
  print_context true None (Lib.contents_after None)

let print_full_context_typ () =
  print_context false None (Lib.contents_after None)

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

let print_sec_context sec = 
  print_context true None (read_sec_context sec)

let print_sec_context_typ sec =
  print_context false None (read_sec_context sec)

let print_eval red_fun env {uj_val=trm;uj_type=typ} =
  let ntrm = red_fun env Evd.empty trm in
  (str "     = " ++ print_judgment env {uj_val = ntrm; uj_type = typ})

let print_name ref = 
  match locate_any_name ref with
  | Term (ConstRef sp) -> print_constant_with_infos sp
  | Term (IndRef (sp,_)) -> print_inductive sp
  | Term (ConstructRef ((sp,_),_)) -> print_inductive sp
  | Term (VarRef sp) -> print_section_variable sp
  | Syntactic kn -> print_syntactic_def " := " kn
  | Dir (DirModule(dirpath,(mp,_))) -> print_module (printable_body dirpath) mp
  | Dir _ -> mt ()
  | ModuleType (_,kn) -> print_modtype kn
  | Undefined qid ->
  try  (* Var locale de but, pas var de section... donc pas d'implicits *)
    let dir,str = repr_qualid qid in 
    if (repr_dirpath dir) <> [] then raise Not_found;
    let (_,c,typ) = Global.lookup_named str in 
    (print_named_decl (str,c,typ))
  with Not_found ->
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
    match print_leaf_entry true " = " (oname,lobj) with
      | None -> mt ()
      | Some pp -> pp ++ fnl()
  with Not_found ->
    errorlabstrm
      "print_name" (pr_qualid qid ++ spc () ++ str "not a defined object")

let print_opaque_name qid = 
  let sigma = Evd.empty in
  let env = Global.env () in
  let sign = Global.named_context () in
  match global qid with
    | ConstRef cst ->
	let cb = Global.lookup_constant cst in
        if cb.const_body <> None then
	  print_constant_with_infos cst
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

let print_about ref = 
  let sigma = Evd.empty in
  let k = locate_any_name ref in
  begin match k with
  | Term ref -> print_ref false ref ++ print_name_infos ref
  | Syntactic kn -> print_syntactic_def " := " kn
  | Dir _ | ModuleType _ | Undefined _ -> mt () end
  ++
  hov 0 (str "Expands to: " ++ pr_located_qualid k)

let print_impargs ref =
  let ref = Nametab.global ref in
  let impl = implicits_of_global ref in
  let has_impl = List.filter is_status_implicit impl <> [] in
  (* Need to reduce since implicits are computed with products flattened *)
  print_ref (need_expansion impl ref) ref ++ fnl() ++
  (if has_impl then print_impl_args impl 
   else (str "No implicit arguments" ++ fnl ()))

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
  print_context false (Some depth) (Lib.contents_after None)


(*************************************************************************)
(* Pretty-printing functions coming from classops.ml                     *)

open Classops

let print_coercion_value v = prterm (get_coercion_value v)

let print_class i =
  let cl,_ = class_info_from_index i in
  pr_class cl
  
let print_path ((i,j),p) = 
  (str"[" ++ 
     prlist_with_sep pr_semicolon print_coercion_value p ++
     str"] : " ++ print_class i ++ str" >-> " ++
     print_class j)

let _ = Classops.install_path_printer print_path

let print_graph () = 
  prlist_with_sep pr_fnl print_path (inheritance_graph())

let print_classes () = 
  prlist_with_sep pr_spc pr_class (classes())

let print_coercions () = 
  prlist_with_sep pr_spc print_coercion_value (coercions())
  
let index_of_class cl =
  try 
    fst (class_info cl)
  with _ -> 
    errorlabstrm "index_of_class" (pr_class cl ++ str" is not a defined class")

let print_path_between cls clt = 
  let i = index_of_class cls in
  let j = index_of_class clt in
  let p = 
    try 
      lookup_path_between (i,j) 
    with _ -> 
      errorlabstrm "index_cl_of_id"
        (str"No path between " ++ pr_class cls ++ str" and " ++ pr_class clt)
  in
  print_path ((i,j),p)

(*************************************************************************)
