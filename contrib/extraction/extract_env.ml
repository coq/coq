
open Pp
open Term
open Lib
open Extraction
open Miniml
open Mlutil

(*s Topological sort of global CIC references. 
    We introduce graphs of global references; a graph is a map
    from edges to the set of their immediate successors. *)

module Refmap = 
  Map.Make(struct type t = global_reference let compare = compare end)

module Refset = 
  Set.Make(struct type t = global_reference let compare = compare end)

type graph = Refset.t Refmap.t

let empty = Refmap.empty

let add_arc x y g =
  let s = try Refmap.find x g with Not_found -> Refset.empty in
  let g' = Refmap.add x (Refset.add y s) g in
  if not (Refmap.mem y g') then Refmap.add y Refset.empty g' else g'

exception Found of global_reference

let maximum g =
  try 
    Refmap.iter (fun x s -> if s = Refset.empty then raise (Found x)) g;
    assert false
  with Found m -> 
    m

let remove m g =
  let g' = 
    Refmap.fold (fun x s -> Refmap.add x (Refset.remove m s)) g Refmap.empty
  in
  Refmap.remove m g'

let sorted g =
  let rec sorted_aux acc g =
    if g = Refmap.empty then
      acc
    else
      let max = maximum g in
      sorted_aux (max :: acc) (remove max g)
  in
  sorted_aux [] g

(*s Computation of the global references appearing in an AST of a 
    declaration. *)

let globals_of_type t =
  let rec collect s = function
    | Tglob r -> Refset.add r s
    | Tapp l -> List.fold_left collect s l
    | Tarr (t1,t2) -> collect (collect s t1) t2
    | Tvar _ | Tprop | Tarity -> s
  in
  collect Refset.empty t

let globals_of_ast a =
  let rec collect s = function
    | MLglob r -> Refset.add r s
    | MLapp (a,l) -> List.fold_left collect (collect s a) l
    | MLlam (_,a) -> collect s a
    | MLletin (_,a,b) -> collect (collect s a) b
    | MLcons (r,_,l) -> List.fold_left collect (Refset.add r s) l
    | MLcase (a,br) -> 
	Array.fold_left 
	  (fun s (r,_,a) -> collect (Refset.add r s) a) (collect s a) br
    | MLfix (_,_,l) -> List.fold_left collect s l
    | MLcast (a,t) -> Refset.union (collect s a) (globals_of_type t)
    | MLmagic a -> collect s a
    | MLrel _ | MLprop | MLarity | MLexn _ -> s
  in
  collect Refset.empty a

let globals_of_inductive inds =
  let globals_of_constructor ie (r,tl) =
    List.fold_left 
      (fun (i,e) t -> Refset.add r i, Refset.union (globals_of_type t) e) ie tl
  in
  let globals_of_ind (i,e) (_,r,cl) = 
    List.fold_left globals_of_constructor (Refset.add r i, e) cl
  in
  let (i,e) = List.fold_left globals_of_ind (Refset.empty,Refset.empty) inds in
  Refset.diff e i

let globals_of_decl = function
  | Dtype inds ->
      globals_of_inductive inds
  | Dabbrev (r,_,t) ->
      Refset.remove r (globals_of_type t)
  | Dglob (r,a) ->
      Refset.remove r (globals_of_ast a)

(*s Recursive extraction of a piece of environment. *)

let add_dependency r r' g = 
  let normalize = function
    | ConstructRef ((sp,_),_) -> IndRef (sp,0)
    | IndRef (sp,i) as r -> if i = 0 then r else IndRef (sp,0)
    | r -> r
  in
  add_arc (normalize r') (normalize r) g

let extract_env rl =
  let rec extract graph seen todo = 
    if Refset.equal todo Refset.empty then
      sorted graph
    else 
      let r = Refset.choose todo in
      let todo' = Refset.remove r todo in
      if Refset.mem r seen then
	extract graph seen todo'
      else
	let d = extract_declaration r in
	let deps = globals_of_decl d in
	let graph' = Refset.fold (add_dependency r) deps graph in
	extract graph' (Refset.add r seen) (Refset.union todo' deps)
  in
  extract empty Refset.empty (List.fold_right Refset.add rl Refset.empty)


(*s Registration of vernac commands for extraction. *)

module ToplevelParams = struct
  let rename_global r = Names.id_of_string (Global.string_of_global r)
  let pp_type_global = Printer.pr_global
  let pp_global = Printer.pr_global
end

module Pp = Ocaml.Make(ToplevelParams)

open Vernacinterp

let _ = 
  overwriting_vinterp_add "Extraction"
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

let reference_of_varg = function
  | VARG_QUALID q -> Nametab.locate q
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
