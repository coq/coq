
(* $Id$ *)

open Util
open Pp
open Names
open Libobject
open Declarations
open Term

let roots = ref []
let push_library_root s = roots := list_add_set s !roots

type cci_table = global_reference Stringmap.t
type obj_table = (section_path * obj) Stringmap.t
type mod_table = (section_path * module_contents) Stringmap.t
and module_contents = Closed of cci_table * obj_table * mod_table

let empty =
  Closed (Stringmap.empty, Stringmap.empty, Stringmap.empty)
 
let nametabs = ref (empty : module_contents)

let push_cci (Closed (ccitab, objtab, modtab)) s ref =
  Closed (Stringmap.add s ref ccitab, objtab, modtab)

let push_obj (Closed (ccitab, objtab, modtab)) s obj =
  Closed (ccitab, Stringmap.add s obj objtab, modtab)

let push_mod (Closed (ccitab, objtab, modtab)) s mc =
  (* devrait pas mais ca plante en décommentant la ligne ci-dessous *)
 (* assert (not (Stringmap.mem s modtab)); *)
  Closed (ccitab, objtab, Stringmap.add s mc modtab)

let push_tree push dir id o =
  let rec search (Closed (ccitab, objtab, modtab) as tabs) pref = function
    | id :: dir' ->
	let sp, mc = 
	  try Stringmap.find id modtab
	  with Not_found ->
	    let pref = List.rev pref in
	    let dir = if pref@[id] = coq_root then [] else pref in
	    (make_path dir (id_of_string id) CCI, empty)
	in
	Closed (ccitab, objtab,
		Stringmap.add id (sp,search mc (id::pref) dir') modtab)
    | [] ->
	push tabs id o
  in nametabs := search !nametabs [] dir

(* This pushes a name at the current level (for relative qualified use) *)
let push_cci_current = push_tree push_cci []
let push_obj_current = push_tree push_obj []
let push_mod_current = push_tree push_mod []

(* This pushes a name at the root level (for absolute access) *)
let push_cci_absolute = push_tree push_cci
let push_obj_absolute = push_tree push_obj
let push_mod_absolute = push_tree push_mod

(* These are entry points for new declarations at toplevel *)
(* Do not use with "open" since it pushes an absolute name too *)
let push sp ref =
  let dir, s = repr_qualid (qualid_of_sp sp) in
  push_cci_absolute dir s ref;
  push_cci_current s ref

let push_object sp obj =
  let dir, s = repr_qualid (qualid_of_sp sp) in
  push_obj_absolute dir s (sp,obj);
  push_obj_current s (sp,obj)

let push_module sp mc =
  let dir, s = repr_qualid (qualid_of_sp sp) in
  push_mod_absolute dir s (sp,mc);
  if List.mem s !roots then 
    warning ("Cannot allow access to "^s^" by relative paths: it is already registered as a root of the Coq library")
  else push_mod_current s (sp,mc)

(* These are entry points to locate names *)
(* If the name starts with the coq_root name, then it is an absolute name *)
let locate qid =
  let (dir,id) = repr_qualid qid in
  let rec search (Closed (ccitab,_,modtab)) = function
    | id :: dir' -> search (snd (Stringmap.find id modtab)) dir'
    | [] -> Stringmap.find id ccitab
  in search !nametabs dir

let locate_obj qid =
  let (dir,id) = repr_qualid qid in
  let rec search (Closed (_,objtab,modtab)) = function
    | id :: dir' -> search (snd (Stringmap.find id modtab)) dir'
    | [] -> Stringmap.find id objtab
  in search !nametabs dir

let locate_module qid =
  let (dir,id) = repr_qualid qid in
  let rec search (Closed (_,_,modtab)) = function
    | id :: dir' -> search (snd (Stringmap.find id modtab)) dir'
    | [] -> Stringmap.find id modtab
  in search !nametabs dir

let locate_constant qid =
  match locate qid with
    | ConstRef sp -> sp
    | _ -> raise Not_found

let sp_of_id _ id = locate (make_qualid [] (string_of_id id))

let constant_sp_of_id id =
  match locate (make_qualid [] (string_of_id id)) with
    | ConstRef sp -> sp
    | _ -> raise Not_found

(* These are entry points to make the contents of a module/section visible *)
(* in the current env (does not affect the absolute name space `coq_root') *)
let open_module_contents qid =
  let _, (Closed (ccitab,objtab,modtab)) = locate_module qid in
  Stringmap.iter push_cci_current ccitab;
(*  Stringmap.iter (fun _ -> Libobject.open_object) objtab;*)
  Stringmap.iter push_mod_current modtab

let rec rec_open_module_contents qid =
  let _, (Closed (ccitab,objtab,modtab)) = locate_module qid in
  Stringmap.iter push_cci_current ccitab;
(*  Stringmap.iter (fun _ -> Libobject.open_object) objtab;*)
  Stringmap.iter 
    (fun m (sp,_ as mt) -> 
       push_mod_current m mt;
       rec_open_module_contents (qualid_of_sp sp))
    modtab

let exists_cci sp =
  try let _ = locate (qualid_of_sp sp) in true with Not_found -> false

(***********************************************)
(* Registration as a global table and rollback *)
    
let init () = nametabs := empty; roots := []

type frozen = module_contents * dir_path list

let freeze () = !nametabs, !roots
		  
let unfreeze (mc,r) = nametabs := mc; roots := r

let _ = 
  Summary.declare_summary "names"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_section = true }

let rollback f x =
  let fs = freeze () in
  try f x with e -> begin unfreeze fs; raise e end

