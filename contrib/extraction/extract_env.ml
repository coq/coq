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
open Names
open Nameops
open Term
open Lib
open Extraction
open Miniml
open Table
open Mlutil
open Nametab
open Vernacinterp
open Common
open Declare

(*s Auxiliary functions dealing with modules. *)

module Dirset =
  Set.Make(struct type t = dir_path let compare = compare end)

let module_of_id m = 
  try 
    locate_loaded_library (make_short_qualid m) 
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
  let rm = String.capitalize (string_of_id (short_module r)) in 
  if rm = sm && not (is_long_module m r) 
  then clash_error sm m (library_part r)

let check_decl m sm = function 
  | Dglob (r,_) -> check_r m sm r 
  | Dabbrev (r,_,_) -> check_r m sm r
  | Dtype ((_,r,_)::_, _) -> check_r m sm r 
  | Dtype ([],_) -> ()
  | Dcustom (r,_) ->  check_r m sm r

(* [check_one_module m l] checks that no module names in [l] clashes with [m]. *)

let check_one_module m l = 
  let sm = String.capitalize (string_of_id (snd (split_dirpath m))) in 
  List.iter (check_decl m sm) l

(* [check_modules m] checks if there are conflicts within the set [m] of modules dirpath. *) 

let check_modules m = 
  let map = ref Idmap.empty in 
  Dirset.iter 
    (fun m -> 
       let sm = String.capitalize (string_of_id (snd (split_dirpath m))) in 
       let idm = id_of_string sm in 
       try 
	 let m' = Idmap.find idm !map in clash_error sm m m'
       with Not_found -> map := Idmap.add idm m !map) m
    
(*s [extract_module m] returns all the global reference declared 
  in a module. This is done by traversing the segment of module [m]. 
  We just keep constants and inductives. *)

let extract_module m =
  let seg = Library.module_segment (Some m) in
  let get_reference = function
    | sp, Leaf o ->
	(match Libobject.object_tag o with
	   | "CONSTANT" | "PARAMETER" -> ConstRef sp
	   | "INDUCTIVE" -> IndRef (sp,0)
	   | _ -> failwith "caught")
    | _ -> failwith "caught"
  in
  Util.map_succeed get_reference seg

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
      let m_name = library_part r' in 
      if not (Dirset.mem m_name eenv.modules) then begin
	eenv.modules <- Dirset.add m_name eenv.modules;
	List.iter (visit_reference m eenv) (extract_module m_name)
      end
    end;
    visit_decl m eenv (extract_declaration r);
    eenv.to_extract <- r' :: eenv.to_extract
  end
    
and visit_type m eenv t =
  let rec visit = function
    | Tglob r -> visit_reference m eenv r
    | Tapp l -> List.iter visit l
    | Tarr (t1,t2) -> visit t1; visit t2
    | Tvar _ | Texn _ | Tprop | Tarity -> ()
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
    | MLrel _ | MLprop | MLarity | MLexn _ -> ()
  in
  visit a

and visit_inductive m eenv inds =
  let visit_constructor (_,tl) = List.iter (visit_type m eenv) tl in
  let visit_ind (_,_,cl) = List.iter visit_constructor cl in
  List.iter visit_ind inds

and visit_decl m eenv = function
  | Dtype (inds,_) ->
      visit_inductive m eenv inds
  | Dabbrev (_,_,t) ->
      visit_type m eenv t
  | Dglob (_,a) ->
      visit_ast m eenv a
  | Dcustom _ -> ()
	
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
  List.iter (visit_reference true eenv) (extract_module m);
  eenv.modules, List.rev eenv.to_extract

(*s Extraction in the Coq toplevel. We display the extracted term in
    Ocaml syntax and we use the Coq printers for globals. The
    vernacular command is \verb!Extraction! [term]. Whenever [term] is
    a global, its definition is displayed. *)

let refs_set_of_list l = List.fold_right Refset.add l Refset.empty 

let decl_of_refs refs = List.map extract_declaration (extract_env refs)

let local_optimize refs = 
  let prm = 
    { lang = Ocaml ; toplevel = true; modular = false;
      mod_name = id_of_string ""; to_appear = refs} in
  optimize prm (decl_of_refs refs)

let print_user_extract r = 
  msgnl (str "User defined extraction:" ++ 
	   spc () ++ str (find_ml_extraction r) ++ fnl ())

let decl_in_r r0 = function 
  | Dglob (r,_) -> r = r0
  | Dabbrev (r,_,_) -> r = r0
  | Dtype ((_,r,_)::_, _) -> sp_of_r r = sp_of_r r0
  | Dtype ([],_) -> false
  | Dcustom (r,_) ->  r = r0 

let extract_reference r =
  if is_ml_extraction r then
    print_user_extract r 
  else
    let d = list_last (local_optimize [r]) in
    msgnl (ToplevelPp.pp_decl 
	     (if (decl_in_r r d) || d = Dtype([],true) || d = Dtype([],false) 
	     then d 
	     else List.find (decl_in_r r) (local_optimize [r])))

let _ = 
  vinterp_add "Extraction"
    (function 
       | [VARG_CONSTR ast] ->
	   (fun () -> 
	      let c = Astterm.interp_constr Evd.empty (Global.env()) ast in
	      match kind_of_term c with
		(* If it is a global reference, then output the declaration *)
		| Const sp -> extract_reference (ConstRef sp)
		| Ind ind -> extract_reference (IndRef ind)
		| Construct cs -> extract_reference (ConstructRef cs)
		(* Otherwise, output the ML type or expression *)
		| _ ->
		    match extract_constr (Global.env()) c with
		      | Emltype (t,_,_) -> msgnl (ToplevelPp.pp_type t)
		      | Emlterm a -> msgnl (ToplevelPp.pp_ast (normalize a)))
       | _ -> assert false)

(*s Recursive extraction in the Coq toplevel. The vernacular command is
    \verb!Recursive Extraction! [qualid1] ... [qualidn]. We use [extract_env]
    to get the saturated environment to extract. *)

let _ = 
  vinterp_add "ExtractionRec"
    (fun vl () ->
       let rl = refs_of_vargl vl in 
       let ml_rl = List.filter is_ml_extraction rl in
       let rl = List.filter (fun x -> not (is_ml_extraction x)) rl in 
       let dl = local_optimize rl in
       List.iter print_user_extract ml_rl ;
       List.iter (fun d -> msgnl (ToplevelPp.pp_decl d)) dl)

(*s Extraction to a file (necessarily recursive). 
    The vernacular command is \verb!Extraction "file"! [qualid1] ... [qualidn].
    We just call [extract_to_file] on the saturated environment. *)

let lang_to_lang = function 
  | "ocaml" -> Ocaml 
  | "haskell" -> Haskell 
  | _ -> assert false

let lang_suffix = function 
  | Ocaml -> "ml"
  | Haskell -> "hs"

let filename f lang = 
  let s = lang_suffix lang in 
  if Filename.check_suffix f s then f,id_of_string (Filename.chop_suffix f s) 
  else f^"."^s,id_of_string f

let _ = 
  vinterp_add "ExtractionFile"
    (function 
       | VARG_STRING lang :: VARG_STRING f :: vl ->
	   (fun () -> 
	      let lang = lang_to_lang lang in 
	      let f,m = filename f lang in 
	      let refs = refs_of_vargl vl in
	      let prm = {lang=lang;
			 toplevel=false;
			 modular=false; 
			 mod_name = m;
			 to_appear= refs} in 
	      let decls = decl_of_refs refs in 
	      let decls = add_ml_decls prm decls in 
	      let decls = optimize prm decls in
	      extract_to_file f prm decls)
       | _ -> assert false)

(*s Extraction of a module. The vernacular command is 
  \verb!Extraction Module! [M]. *) 

let decl_in_m m = function 
  | Dglob (r,_) -> is_long_module m r
  | Dabbrev (r,_,_) -> is_long_module m r
  | Dtype ((_,r,_)::_, _) -> is_long_module m r 
  | Dtype ([],_) -> false
  | Dcustom (r,_) ->  is_long_module m r

let module_file_name m = function
  | Ocaml -> (String.uncapitalize (string_of_id m)) ^ ".ml"
  | Haskell -> (String.capitalize (string_of_id m)) ^ ".hs"

let _ = 
  vinterp_add "ExtractionModule"
    (function 
       | [VARG_STRING lang; VARG_IDENTIFIER m] ->
	   (fun () -> 
	      let lang = lang_to_lang lang in 
	      let dir_m = module_of_id m in 
	      let f = module_file_name m lang in
	      let prm = {lang=lang;
			 toplevel=false;
			 modular=true;
			 mod_name= m;
			 to_appear= []} in 
	      let rl = extract_module dir_m in 
	      let decls = optimize prm (decl_of_refs rl) in
	      let decls = add_ml_decls prm decls in 
	      check_one_module dir_m decls; 
	      let decls = List.filter (decl_in_m dir_m) decls in
	      extract_to_file f prm decls)
       | _ -> assert false)

(*s Recursive Extraction of all the modules [M] depends on. 
  The vernacular command is \verb!Recursive Extraction Module! [M]. *) 

let _ = 
  vinterp_add "RecursiveExtractionModule"
        (function 
       | [VARG_STRING lang; VARG_IDENTIFIER m] ->
	   (fun () -> 
	      let lang = lang_to_lang lang in 
	      let dir_m = module_of_id m in 
	      let modules,refs = 
		modules_extract_env dir_m in
	      check_modules modules; 
	      let dummy_prm = {lang=lang;
			      toplevel=false;
			      modular=true;
			      mod_name=m;
			      to_appear= []} in
	      let decls = optimize dummy_prm (decl_of_refs refs) in
	      let decls = add_ml_decls dummy_prm decls in
	      Dirset.iter 
		(fun m ->
		   let short_m = snd (split_dirpath m) in
		   let f = module_file_name short_m lang in 
		   let prm = {lang=lang;
			      toplevel=false;
			      modular=true;
			      mod_name=short_m;
			      to_appear= []} in 
		   let decls = List.filter (decl_in_m m) decls in
		   if decls <> [] then extract_to_file f prm decls)
		modules)
       | _ -> assert false)
