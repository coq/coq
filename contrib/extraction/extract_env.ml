(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Pp
open Util
open Declarations
open Names
open Nameops
open Libnames
open Miniml
open Table
open Extraction
open Mlutil
open Common

(*

let mp_of_kn kn = 
  let mp,_,l = repr_kn kn in MPdot (mp,l) 


let toplevel_structure_body () = 
  let seg = Lib.contents_after None in 
  let get_reference = function 
    | (_,kn), Lib.Leaf o ->
	let mp,_,l = repr_kn kn in 
	let seb = match Libobject.object_tag o with
	  | "CONSTANT" -> SEBconst (Global.lookup_constant kn)
	  | "INDUCTIVE" -> SEBmind (Global.lookup_mind kn) 
	  | "MODULE" -> SEBmodule (Global.lookup_module (MPdot (mp,l)))
	  | "MODULE TYPE" -> SEBmodtype (Global.lookup_modtype kn)
	  | _ -> failwith "caught"
	in l,seb
    | _ -> failwith "caught"
  in 
  List.rev (map_succeed get_reference seg)


let environment_until dir_opt = 
  let rec parse = function 
    | [] -> [] 
    | d :: l when dir_opt = Some d -> []
    | d :: l -> 
	match (Global.lookup_module (MPfile d)).mod_expr with 
	  | Some (MEBstruct (_, msb)) -> (d, msb) :: (parse l)
	  | _ -> assert false
  in parse (Library.loaded_libraries ())

let std_kn mp l = make_kn mp empty_dirpath l

let rec sub_modpath mp = match mp with 
  | MPdot (mp',_) -> MPset.add mp (sub_modpath mp')
  | _ -> MPset.singleton mp

type visit = { mutable kn : KNset.t; mutable mp : MPset.t }

let in_kn kn v = KNset.mem kn v.kn
let in_mp mp v = MPset.mem mp v.mp

let rec visit_type m eenv t =
  let rec visit = function
    | Tglob (r,l) -> visit_reference m eenv r; List.iter visit l  
    | Tarr (t1,t2) -> visit t1; visit t2
    | Tvar _ | Tdummy | Tunknown | Tcustom _ -> ()
    | Tmeta _ | Tvar' _ -> assert false 
  in
  visit t
    
and visit_ast m eenv a =
  let rec visit = function
    | MLglob r -> visit_reference m eenv r
    | MLapp (a,l) -> visit a; List.iter visit l
    | MLlam (_,a) -> visit a
    | MLletin (_,a,b) -> visit a; visit b
    | MLcons (r,l) -> visit_reference m eenv r; List.iter visit l
    | MLcase (a,br) -> 
	visit a; 
	Array.iter (fun (r,_,a) -> visit_reference m eenv r; visit a) br
    | MLfix (_,_,l) -> Array.iter visit l
    | MLcast (a,t) -> visit a; visit_type m eenv t
    | MLmagic a -> visit a
    | MLrel _ | MLdummy | MLexn _ | MLcustom _ -> ()
  in
  visit a

and visit_inductive m eenv inds =
  let visit_constructor (_,tl) = List.iter (visit_type m eenv) tl in
  let visit_ind (_,_,cl) = List.iter visit_constructor cl in
  List.iter visit_ind inds

and visit_decl m eenv = function
  | Dind (inds,_) -> visit_inductive m eenv inds
  | Dtype (_,_,t) -> visit_type m eenv t
  | Dterm (_,a,t) -> visit_ast m eenv a; visit_type m eenv t
  | Dfix (_,c,t) -> 
      Array.iter (visit_ast m eenv) c;
      Array.iter (visit_type m eenv) t
  | _ -> ()


let rec get_structure_elem_references = function 
  | SEind ml_ind -> 
      
let rec extract_msb mp all v = function 
  | [] -> [] 
  | (l,seb) -> 
      let ml_msb = extract_msb v in 
      match seb with 
	| SEBconst cb -> 
	    let kn = std_kn mp l in 
	    if all || in_kn kn v then 
	      let ml_se = extraction_constant_body kn cb in 
	      get_structure_elem_references ml_se v; 
	      ml_se :: ml_msb
	    else ml_msb
	| SEBmind mib ->
	    let kn = std_kn mp l in 
	    if all || in_kn kn v then 
	      let ml_se = extraction_inductive_body kn mib in
	      search_visit ml_se v;
	      ml_se :: ml_msb 
	    else ml_msb
	| SEBmodule mb -> 
	    let mp = MPdot (mp,l) in 
	    if all || in_mp mp v then 
	      SEmodule (extraction_module mp true v m) :: ml_msb
	    else msb
	| SEBmodtype mtb ->
	    let kn = std_kn mp l in
	    if all || in_kn kn v then 
	      SEmodtype (extraction_mtb (MPdot (mp,l)) true v m) :: ml_msb
	    else msb


let mono_environment kn_set = 
  let add_mp kn mpset = KNset.union (sub_modpath (modpath kn)) mpset
  let kn_to_visit = ref kn_set 
  and mp_to_visit = ref (KNset.fold add_mp kn_set MPset.empty)
  in 
  
  let rec extract_structure_body = 


  let top = toplevel_structure_body ()

*)

(*s Auxiliary functions dealing with modules. *)

let dir_module_of_id m = 
  try 
    Nametab.locate_loaded_library (make_short_qualid m) 
  with Not_found ->  
    errorlabstrm "module_message"
      (str "Module" ++ spc () ++ pr_id m ++ spc () ++ str "not found.") 

(*s Module name clash verification. *)

let clash_error sn n1 n2 = 
  errorlabstrm "clash_module_message"
    (str ("There are two Coq modules with ML name " ^ sn ^" :") ++ 
     fnl () ++ str ("  "^(string_of_dirpath n1)) ++ 
     fnl () ++ str ("  "^(string_of_dirpath n2)) ++ 
     fnl () ++ str "This is not allowed in ML. Please do some renaming first.")
    
let check_r m sm r = 
  let rlm = long_module r in 
  let rsm = List.hd (repr_dirpath rlm) in 
  if (String.capitalize (string_of_id rsm)) = sm && m <> rlm
  then clash_error sm m rlm
    
let check_decl m sm = function 
  | Dterm (r,_,_) -> check_r m sm r 
  | Dtype (r,_,_) -> check_r m sm r
  | Dind ((_,r,_)::_, _) -> check_r m sm r 
  | Dind ([],_) -> ()
  | DcustomTerm (r,_) ->  check_r m sm r
  | DcustomType (r,_) ->  check_r m sm r	
  | Dfix(rv,_,_) -> Array.iter (check_r m sm) rv 

(* [check_one_module] checks that no module names in [l] clashes with [m]. *)

let check_one_module m l = 
  let sm = String.capitalize (string_of_id (snd (split_dirpath m))) in 
  List.iter (check_decl m sm) l

(* [check_modules] checks if there are conflicts within the set [m] 
   of modules dirpath. *) 

let check_modules m = 
  let map = ref Idmap.empty in 
  Dirset.iter 
    (fun m -> 
       let sm = String.capitalize (string_of_id (snd (split_dirpath m))) in 
       let idm = id_of_string sm in 
       try 
	 let m' = Idmap.find idm !map in clash_error sm m m'
       with Not_found -> map := Idmap.add idm m !map) m
    
(*s Recursive computation of the global references to extract. 
    We use a set of functions visiting the extracted objects in
    a depth-first way ([visit_type], [visit_ast] and [visit_decl]).
    We maintain an (imperative) structure [extracted_env] containing
    the set of already visited references and the list of 
    references to extract. The entry point is the function [visit_reference]:
    it first normalizes the reference, and then check it has already been 
    visisted; if not, it adds it to the set of visited references, then
    recursively traverses its extraction and finally adds it to the 
    list of references to extract. *) 

type extracted_env = {
  mutable visited : Refset.t;
  mutable to_extract : global_reference list;
  mutable modules : Dirset.t
}

let empty () = 
  { visited = ml_extractions (); 
    to_extract = []; 
    modules = Dirset.empty }

let rec visit_reference m eenv r =
  let r' = match r with
    | ConstructRef ((sp,_),_) -> IndRef (sp,0)
    | IndRef (sp,i) -> if i = 0 then r else IndRef (sp,0)
    | _ -> r
  in
  if not (Refset.mem r' eenv.visited) then begin
    (* we put [r'] in [visited] first to avoid loops in inductive defs 
       and in module extraction *)
    eenv.visited <- Refset.add r' eenv.visited;
    if m then begin 
      let m_name = Declare.library_part r' in 
      if not (Dirset.mem m_name eenv.modules) then begin
	eenv.modules <- Dirset.add m_name eenv.modules;
	List.iter (visit_reference m eenv) (module_contents m_name)
      end
    end;
    visit_decl m eenv (extract_declaration r);
    eenv.to_extract <- r' :: eenv.to_extract
  end

(* and visit_fixpoint m eenv r = 
  match (kind_of_term (constant_value (Global.env()) (kn_of_r r))) with 
    | Fix (_,(f,_,_)) -> 
	(try 
	   let d = dirpath (sp_of_global None r) in 
	   let v = Array.map (fun id -> locate (make_qualid d id)) f in *)

and visit_type m eenv t =
  let rec visit = function
    | Tglob (r,l) -> visit_reference m eenv r; List.iter visit l  
    | Tarr (t1,t2) -> visit t1; visit t2
    | Tvar _ | Tdummy | Tunknown | Tcustom _ -> ()
    | Tmeta _ | Tvar' _ -> assert false 
  in
  visit t
    
and visit_ast m eenv a =
  let rec visit = function
    | MLglob r -> visit_reference m eenv r
    | MLapp (a,l) -> visit a; List.iter visit l
    | MLlam (_,a) -> visit a
    | MLletin (_,a,b) -> visit a; visit b
    | MLcons (r,l) -> visit_reference m eenv r; List.iter visit l
    | MLcase (a,br) -> 
	visit a; 
	Array.iter (fun (r,_,a) -> visit_reference m eenv r; visit a) br
    | MLfix (_,_,l) -> Array.iter visit l
    | MLcast (a,t) -> visit a; visit_type m eenv t
    | MLmagic a -> visit a
    | MLrel _ | MLdummy | MLexn _ | MLcustom _ -> ()
  in
  visit a

and visit_inductive m eenv inds =
  let visit_constructor (_,tl) = List.iter (visit_type m eenv) tl in
  let visit_ind (_,_,cl) = List.iter visit_constructor cl in
  List.iter visit_ind inds

and visit_decl m eenv = function
  | Dind (inds,_) -> visit_inductive m eenv inds
  | Dtype (_,_,t) -> visit_type m eenv t
  | Dterm (_,a,t) -> visit_ast m eenv a; visit_type m eenv t
  | Dfix (_,c,t) -> 
      Array.iter (visit_ast m eenv) c;
      Array.iter (visit_type m eenv) t
  | _ -> ()
	
(*s Recursive extracted environment for a list of reference: we just
    iterate [visit_reference] on the list, starting with an empty
    extracted environment, and we return the reversed list of 
    references in the field [to_extract], and the visited_modules in 
    case of recursive module extraction *)

let extract_env rl =
  let eenv = empty () in
  List.iter (visit_reference false eenv) rl;
  List.rev eenv.to_extract

let modules_extract_env m =
  let eenv = empty () in
  eenv.modules <- Dirset.singleton m;
  List.iter (visit_reference true eenv) (module_contents m);
  eenv.modules, List.rev eenv.to_extract

(* let toplevel_contents () = 
  segment_contents (contents_after None)

let extract_env rl = 
  let modules = List.rev (loaded_libraries ()) in 
  let toplevel_list = toplevel_contents () in 
  let modules_list = *)


(*s Extraction in the Coq toplevel. We display the extracted term in
    Ocaml syntax and we use the Coq printers for globals. The
    vernacular command is \verb!Extraction! [qualid]. *)

let decl_of_refs refs = List.map extract_declaration (extract_env refs)

let print_user_extract r = 
  msgnl (str "User defined extraction:" ++ 
	   spc () ++ str (find_ml_extraction r) ++ fnl ())

let decl_in_r r0 = function 
  | Dterm (r,_,_) -> r = r0
  | Dtype (r,_,_) -> r = r0
  | Dind ((_,r,_)::_, _) -> kn_of_r r = kn_of_r r0
  | Dind ([],_) -> false
  | DcustomTerm (r,_) ->  r = r0 
  | DcustomType (r,_) ->  r = r0 
  | Dfix (rv,_,_) -> array_exists ((=) r0) rv

let extraction qid =
  let r = Nametab.global qid in 
  if is_ml_extraction r then
    print_user_extract r 
  else if decl_is_logical_ind r then 
    msgnl (pp_logical_ind r) 
  else if decl_is_singleton r then 
    msgnl (pp_singleton_ind r) 
  else 
    let prm = 
      { modular = false; mod_name = id_of_string "Main"; to_appear = [r]} in 
    let decls = optimize prm (decl_of_refs [r]) in 
    let d = list_last decls in
    let d = if (decl_in_r r d) then d 
    else List.find (decl_in_r r) decls in 
    set_keywords ();
    create_mono_renamings decls; 
    msgnl (pp_decl () d)

(*s Recursive extraction in the Coq toplevel. The vernacular command is
    \verb!Recursive Extraction! [qualid1] ... [qualidn]. We use [extract_env]
    to get the saturated environment to extract. *)

let mono_extraction (f,m) vl = 
  let refs = List.map Nametab.global vl in
  let prm = {modular=false; mod_name = m; to_appear= refs} in
  let decls = decl_of_refs refs in 
  let decls = add_ml_decls prm decls in 
  let decls = optimize prm decls in
  extract_to_file f prm decls

let extraction_rec = mono_extraction (None,id_of_string "Main")

(*s Extraction to a file (necessarily recursive). 
    The vernacular command is \verb!Extraction "file"! [qualid1] ... [qualidn].
    We just call [extract_to_file] on the saturated environment. *)

let lang_suffix () = match lang () with 
  | Ocaml -> ".ml"
  | Haskell -> ".hs"
  | Scheme -> ".scm"
  | Toplevel -> assert false

let filename f = 
  let s = lang_suffix () in 
  if Filename.check_suffix f s then 
    Some f,id_of_string (Filename.chop_suffix f s) 
  else Some (f^s),id_of_string f

let toplevel_error () = 
  errorlabstrm "toplevel_extraction_language"
    (str "Toplevel pseudo-ML language cannot be used outside Coq toplevel." 
     ++ fnl () ++
     str "You should use Extraction Language Ocaml or Haskell before.") 

let extraction_file f vl =
  if lang () = Toplevel then toplevel_error () 
  else mono_extraction (filename f) vl

(*s Extraction of a module. The vernacular command is 
  \verb!Extraction Module! [M]. *) 

let decl_in_m m = function 
  | Dterm (r,_,_) -> m = long_module r
  | Dtype (r,_,_) -> m = long_module r
  | Dind ((_,r,_)::_, _) -> m = long_module r 
  | Dind ([],_) -> false
  | DcustomTerm (r,_) ->  m = long_module r
  | DcustomType (r,_) ->  m = long_module r
  | Dfix (rv,_,_) -> m = long_module rv.(0)

let module_file_name m = match lang () with 
  | Ocaml -> (String.uncapitalize (string_of_id m)) ^ ".ml"
  | Haskell -> (String.capitalize (string_of_id m)) ^ ".hs"
  | _ -> assert false

let scheme_error () = 
  errorlabstrm "scheme_extraction_language"
    (str "No Scheme modular extraction available yet." ++ fnl ())

let extraction_module m =
  match lang () with 
    | Toplevel -> toplevel_error ()
    | Scheme -> scheme_error ()
    | _ -> 
	let dir_m = dir_module_of_id m in 
	let f = module_file_name m in
	let prm = {modular=true; mod_name=m; to_appear=[]} in 
	let rl = module_contents dir_m in 
	let decls = optimize prm (decl_of_refs rl) in
	let decls = add_ml_decls prm decls in 
	check_one_module dir_m decls; 
	let decls = List.filter (decl_in_m dir_m) decls in
	extract_to_file (Some f) prm decls
	  
(*s Recursive Extraction of all the modules [M] depends on. 
  The vernacular command is \verb!Recursive Extraction Module! [M]. *) 

let recursive_extraction_module m =
  match lang () with 
    | Toplevel -> toplevel_error () 
    | Scheme -> scheme_error () 
    | _ -> 
	let dir_m = dir_module_of_id m in 
	let modules,refs = modules_extract_env dir_m in
	check_modules modules; 
	let dummy_prm = {modular=true; mod_name=m; to_appear=[]} in
	let decls = optimize dummy_prm (decl_of_refs refs) in
	let decls = add_ml_decls dummy_prm decls in
	Dirset.iter 
	  (fun m ->
	     let short_m = snd (split_dirpath m) in
	     let f = module_file_name short_m in 
	     let prm = {modular=true;mod_name=short_m;to_appear=[]} in 
	     let decls = List.filter (decl_in_m m) decls in
	     if decls <> [] then extract_to_file (Some f) prm decls)
	  modules
