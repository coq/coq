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
open Term
open Lib
open Extraction
open Miniml
open Table
open Mlutil
open Vernacinterp
open Common

(*s [extract_module m] returns all the global reference declared in a module *)

let extract_module m =
  let m = Nametab.locate_loaded_library (Nametab.make_short_qualid m) in
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
  mutable modules : identifier list
}

let empty () = 
  { visited = ml_extractions (); to_extract = []; modules = []}

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
      let m_name = module_of_r r' in 
      if not (List.mem m_name eenv.modules) then begin
	eenv.modules <- m_name :: eenv.modules;
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
    | Tvar _ | Tprop | Tarity -> ()
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
	visit a; Array.iter (fun (r,_,a) -> visit_reference m eenv r; visit a) br
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
  eenv.modules <- [m];
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
    { lang = "ocaml" ; toplevel = true; 
      mod_name = None; to_appear = refs} in
  optimize prm (decl_of_refs refs)

let print_user_extract r = 
  mSGNL [< 'sTR "User defined extraction:"; 'sPC; 'sTR (find_ml_extraction r) ; 'fNL>]

let extract_reference r =
  if is_ml_extraction r then
    print_user_extract r 
  else
    mSGNL (ToplevelPp.pp_decl (list_last (local_optimize [r])))

let _ = 
  vinterp_add "Extraction"
    (function 
       | [VARG_CONSTR ast] ->
	   (fun () -> 
	      let c = Astterm.interp_constr Evd.empty (Global.env()) ast in
	      match kind_of_term c with
		(* If it is a global reference, then output the declaration *)
		| IsConst sp -> extract_reference (ConstRef sp)
		| IsMutInd ind -> extract_reference (IndRef ind)
		| IsMutConstruct cs -> extract_reference (ConstructRef cs)
		(* Otherwise, output the ML type or expression *)
		| _ ->
		    match extract_constr (Global.env()) [] c with
		      | Emltype (t,_,_) -> mSGNL (ToplevelPp.pp_type t)
		      | Emlterm a -> mSGNL (ToplevelPp.pp_ast (normalize a)))
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
       let dl = decl_of_refs rl in
       List.iter print_user_extract ml_rl ;
       List.iter (fun d -> mSGNL (ToplevelPp.pp_decl d)) dl)

(*s Extraction to a file (necessarily recursive). 
    The vernacular command is \verb!Extraction "file"! [qualid1] ... [qualidn].
    We just call [extract_to_file] on the saturated environment. *)

let _ = 
  vinterp_add "ExtractionFile"
    (function 
       | VARG_STRING lang :: VARG_STRING f :: vl ->
	   (fun () -> 
	      let refs = refs_of_vargl vl in
	      let prm = {lang=lang;
			 toplevel=false;
			 mod_name = None;
			 to_appear= refs} in 
	      let decls = decl_of_refs refs in 
	      let decls = add_ml_decls prm decls in 
	      let decls = optimize prm decls in
	      extract_to_file f prm decls)
       | _ -> assert false)

(*s Extraction of a module. The vernacular command is \verb!Extraction Module!
    [M]. We build the environment to extract by traversing the segment of
    module [M]. We just keep constants and inductives, and we remove
    those having an ML extraction. *)

let decl_in_m m = function 
  | Dglob (r,_) -> m = module_of_r r
  | Dabbrev (r,_,_) -> m = module_of_r r
  | Dtype ((_,r,_)::_, _) -> m = module_of_r r 
  | Dtype ([],_) -> false
  | Dcustom (r,_) ->  m = module_of_r r

let file_suffix = function
  | "ocaml" -> ".ml"
  | "haskell" -> ".hs"
  | _ -> assert false

let _ = 
  vinterp_add "ExtractionModule"
    (function 
       | [VARG_STRING lang; VARG_IDENTIFIER m] ->
	   (fun () -> 
	      let f = (String.uncapitalize (string_of_id m))
		       ^ (file_suffix lang) in
	      let prm = {lang=lang;
			 toplevel=false;
			 mod_name= Some m;
			 to_appear= []} in 
	      let rl = extract_module m in 
	      let decls = optimize prm (decl_of_refs rl) in
	      let decls = add_ml_decls prm decls in 
	      let decls = List.filter (decl_in_m m) decls in
	      extract_to_file f prm decls)
       | _ -> assert false)


let _ = 
  vinterp_add "RecursiveExtractionModule"
        (function 
       | [VARG_STRING lang; VARG_IDENTIFIER m] ->
	   (fun () -> 
	      let modules,refs = modules_extract_env m in 
	      let dummy_prm = {lang=lang;
			      toplevel=false;
			      mod_name= Some m;
			      to_appear= []} in
	      let decls = optimize dummy_prm (decl_of_refs refs) in
	      let decls = add_ml_decls dummy_prm decls in
	      List.iter 
		(fun m ->
		   let f = (String.uncapitalize (string_of_id m))
			   ^ (file_suffix lang) in
		   let prm = {lang=lang;
			      toplevel=false;
			      mod_name= Some m;
			      to_appear= []} in 
		   let decls = List.filter (decl_in_m m) decls in
		   extract_to_file f prm decls)
		modules)
       | _ -> assert false)
