
open Pp
open Util
open Term
open Lib
open Extraction
open Miniml
open Mlutil

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
  mutable to_extract : global_reference list 
}

let empty () = { visited = ml_extractions (); to_extract = [] }

let rec visit_reference eenv r =
  let r' = match r with
    | ConstructRef ((sp,_),_) -> IndRef (sp,0)
    | IndRef (sp,i) -> if i = 0 then r else IndRef (sp,0)
    | _ -> r
  in
  if not (Refset.mem r' eenv.visited) then begin
    (* we put [r'] in [visited] first to avoid loops in inductive defs *)
    eenv.visited <- Refset.add r' eenv.visited;
    visit_decl eenv (extract_declaration r);
    eenv.to_extract <- r' :: eenv.to_extract
  end

and visit_type eenv t =
  let rec visit = function
    | Tglob r -> visit_reference eenv r
    | Tapp l -> List.iter visit l
    | Tarr (t1,t2) -> visit t1; visit t2
    | Tvar _ | Tprop | Tarity -> ()
  in
  visit t

and visit_ast eenv a =
  let rec visit = function
    | MLglob r -> visit_reference eenv r
    | MLapp (a,l) -> visit a; List.iter visit l
    | MLlam (_,a) -> visit a
    | MLletin (_,a,b) -> visit a; visit b
    | MLcons (r,_,l) -> visit_reference eenv r; List.iter visit l
    | MLcase (a,br) -> 
	visit a; Array.iter (fun (r,_,a) -> visit_reference eenv r; visit a) br
    | MLfix (_,_,l) -> List.iter visit l
    | MLcast (a,t) -> visit a; visit_type eenv t
    | MLmagic a -> visit a
    | MLrel _ | MLprop | MLarity | MLexn _ -> ()
  in
  visit a

and visit_inductive eenv inds =
  let visit_constructor (_,tl) = List.iter (visit_type eenv) tl in
  let visit_ind (_,_,cl) = List.iter visit_constructor cl in
  List.iter visit_ind inds

and visit_decl eenv = function
  | Dtype inds ->
      visit_inductive eenv inds
  | Dabbrev (_,_,t) ->
      visit_type eenv t
  | Dglob (_,a) ->
      visit_ast eenv a

(*s Recursive extracted environment for a list of reference: we just
    iterate [visit_reference] on the list, starting with an empty
    extracted environment, and we return the reversed list of 
    references in the field [to_extract]. *)

let extract_env rl =
  let eenv = empty () in
  List.iter (visit_reference eenv) rl;
  List.rev eenv.to_extract

(*s Registration of vernac commands for extraction. *)

module ToplevelParams = struct
  let rename_global r = Names.id_of_string (Global.string_of_global r)
  let pp_type_global = Printer.pr_global
  let pp_global = Printer.pr_global
end

module Pp = Ocaml.Make(ToplevelParams)

open Vernacinterp

let _ = 
  vinterp_add "Extraction"
    (function 
       | [VARG_CONSTR ast] ->
	   (fun () -> 
	      let c = Astterm.interp_constr Evd.empty (Global.env()) ast in
	      match kind_of_term c with
		(* If it is a global reference, then output the declaration *)
		| IsConst (sp,_) -> 
		    mSGNL (Pp.pp_decl (extract_declaration (ConstRef sp)))
		| IsMutInd (ind,_) ->
		    mSGNL (Pp.pp_decl (extract_declaration (IndRef ind)))
		| IsMutConstruct (cs,_) ->
		    mSGNL (Pp.pp_decl (extract_declaration (ConstructRef cs)))
		(* Otherwise, output the ML type or expression *)
		| _ ->
		    match extract_constr (Global.env()) [] c with
		      | Emltype (t,_,_) -> mSGNL (Pp.pp_type t)
		      | Emlterm a -> mSGNL (Pp.pp_ast a)
		      | Eprop -> message "prop")
       | _ -> assert false)

let no_such_reference q =
  errorlabstrm "reference_of_varg" 
    [< Nametab.pr_qualid q; 'sTR ": no such reference" >]

let reference_of_varg = function
  | VARG_QUALID q -> 
      (try Nametab.locate q with Not_found -> no_such_reference q)
  | _ -> assert false

let decl_of_vargl vl =
  let rl = List.map reference_of_varg vl in
  List.map extract_declaration (extract_env rl)

let _ = 
  vinterp_add "ExtractionRec"
    (fun vl () ->
       let rl' = decl_of_vargl vl in
       List.iter (fun d -> mSGNL (Pp.pp_decl d)) rl')

let _ = 
  vinterp_add "ExtractionFile"
    (function 
       | VARG_STRING f :: vl ->
	   (fun () -> Ocaml.extract_to_file f false (decl_of_vargl vl))
       | _ -> assert false)

(*s Extraction of a module. *)

let extract_module m =
  let seg = Library.module_segment (Some m) in
  let get_reference = function
    | sp, Leaf o ->
	(match Libobject.object_tag o with
	   | "CONSTANT" -> ConstRef sp
	   | "INDUCTIVE" -> IndRef (sp,0)
	   | _ -> failwith "caught")
    | _ -> failwith "caught"
  in
  let rl = Util.map_succeed get_reference seg in
  List.map extract_declaration rl

let _ = 
  vinterp_add "ExtractionModule"
    (function 
       | [VARG_IDENTIFIER m] ->
	   (fun () -> 
	      let m = Names.string_of_id m in
	      Ocaml.current_module := m;
	      let f = (String.uncapitalize m) ^ ".ml" in
	      Ocaml.extract_to_file f true (extract_module m))
       | _ -> assert false)
