
(* $Id$ *)

open Util
open Pp
open Names
open Libobject
open Declarations
open Term

(*s Roots of the space of absolute names *)

let roots = ref []
let push_library_root s = roots := list_add_set s !roots

let coq_root = "Coq"
let default_root = "Scratch"

(* Names tables *)
type cci_table = global_reference Idmap.t
type obj_table = (section_path * obj) Idmap.t
type mod_table = (section_path * module_contents) Stringmap.t
and module_contents = Closed of cci_table * obj_table * mod_table

let empty =
  Closed (Idmap.empty, Idmap.empty, Stringmap.empty)
 
let persistent_nametab = ref (empty : module_contents)
let local_nametab = ref (empty : module_contents)

let push_cci (Closed (ccitab, objtab, modtab)) s ref =
  Closed (Idmap.add s ref ccitab, objtab, modtab)

let push_obj (Closed (ccitab, objtab, modtab)) s obj =
  Closed (ccitab, Idmap.add s obj objtab, modtab)

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
	    (make_path dir (id_of_string id) CCI, empty)
	in
	Closed (ccitab, objtab,
		Stringmap.add id (sp,search mc (id::pref) dir') modtab)
    | [] ->
	push tabs id o in
  persistent_nametab := search !persistent_nametab [] dir

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
  let s = string_of_id s in
  push_mod_absolute dir s (sp,mc);
  if List.mem s !roots then 
    warning ("Cannot allow access to "^s^" by relative paths: it is already registered as a root of the Coq library")
  else push_mod_current s (sp,mc)

(* Sections are not accessible by basename *)
let push_section sp mc =
  let dir, s = repr_qualid (qualid_of_sp sp) in
  push_mod_absolute dir (string_of_id s) (sp,mc)

(* This is an entry point for local declarations at toplevel *)
(* Do not use with "open" since it pushes an absolute name too *)

let push_cci_local s ref =
  local_nametab := push_cci !local_nametab s ref

let push_obj_local s o =
  local_nametab := push_obj !local_nametab s o

let push_local sp ref =
  let dir, s = repr_qualid (qualid_of_sp sp) in
  push_cci_absolute dir s ref;
  push_cci_local s ref

let push_local_object sp obj =
  let dir, s = repr_qualid (qualid_of_sp sp) in
  push_obj_absolute dir s (sp,obj);
  push_obj_local s (sp,obj)

(* These are entry points to locate names *)
(* If the name starts with the coq_root name, then it is an absolute name *)
let locate qid =
  let (dir,id) = repr_qualid qid in
  let rec search (Closed (ccitab,_,modtab)) = function
    | id :: dir' -> search (snd (Stringmap.find id modtab)) dir'
    | [] -> Idmap.find id ccitab
  in
  try search !local_nametab dir
  with Not_found -> search !persistent_nametab dir

let locate_obj qid =
  let (dir,id) = repr_qualid qid in
  let rec search (Closed (_,objtab,modtab)) = function
    | id :: dir' -> search (snd (Stringmap.find id modtab)) dir'
    | [] -> Idmap.find id objtab
  in
  try search !local_nametab dir
  with Not_found -> search !persistent_nametab dir

let locate_module qid =
  let (dir,id) = repr_qualid qid in
  let s = string_of_id id in
  let rec search (Closed (_,_,modtab)) = function
    | id :: dir' -> search (snd (Stringmap.find id modtab)) dir'
    | [] -> Stringmap.find s modtab
  in
  try search !local_nametab dir
  with Not_found -> search !persistent_nametab dir

let locate_constant qid =
  match locate qid with
    | ConstRef sp -> sp
    | _ -> raise Not_found

let sp_of_id _ id = locate (make_qualid [] id)

let constant_sp_of_id id =
  match locate (make_qualid [] id) with
    | ConstRef sp -> sp
    | _ -> raise Not_found

let check_absoluteness dir =
  match dir with
    | a::_ when List.mem a !roots -> ()
    | _ -> anomaly ("Not an absolute dirpath: "^(string_of_dirpath dir))

let absolute_reference sp =
  check_absoluteness (dirpath sp);
  locate (qualid_of_sp sp)

exception Found of global_reference
let locate_in_module dir id =
  let rec exists_in id (Closed (ccitab,_,modtab)) =
    try raise (Found (Idmap.find id ccitab))
    with Not_found -> 
      Stringmap.iter (fun _ (sp,mc) -> exists_in id mc) modtab
  in
  let rec search (Closed (ccitab,_,modtab) as mc) = function
    | modid :: dir' -> search (snd (Stringmap.find modid modtab)) dir'
    | [] -> 
	try exists_in id mc; raise Not_found
	with Found ref -> ref
  in
  search !persistent_nametab dir

let locate_in_absolute_module dir id =
  check_absoluteness dir;
  locate_in_module dir id

(* These are entry points to make the contents of a module/section visible *)
(* in the current env (does not affect the absolute name space `coq_root') *)
let open_module_contents qid =
  let _, (Closed (ccitab,objtab,modtab)) = locate_module qid in
  Idmap.iter push_cci_current ccitab;
(*  Idmap.iter (fun _ -> Libobject.open_object) objtab;*)
  Stringmap.iter push_mod_current modtab

let conditional_push ref = push_cci_current ref (* TODO *)

let open_section_contents qid =
  let _, (Closed (ccitab,objtab,modtab)) = locate_module qid in
  Idmap.iter push_cci_current ccitab;
(*  Idmap.iter (fun _ -> Libobject.open_object) objtab;*)
  Stringmap.iter push_mod_current modtab

let rec rec_open_module_contents qid =
  let _, (Closed (ccitab,objtab,modtab)) = locate_module qid in
  Idmap.iter push_cci_current ccitab;
(*  Idmap.iter (fun _ -> Libobject.open_object) objtab;*)
  Stringmap.iter 
    (fun m (sp,_ as mt) -> 
       push_mod_current m mt;
       rec_open_module_contents (qualid_of_sp sp))
    modtab

let exists_cci sp =
  try let _ = locate (qualid_of_sp sp) in true with Not_found -> false

let exists_module sp =
  try let _ = locate_module (qualid_of_sp sp) in true with Not_found -> false

(********************************************************************)
(* Registration of persistent tables as a global table and rollback *)

type frozen = module_contents

let init () = persistent_nametab := empty; roots := []
let freeze () = !persistent_nametab, !roots
let unfreeze (mc,r) = persistent_nametab := mc; roots := r

let _ = 
  Summary.declare_summary "persistent-names"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_section = true }

(********************************************************************)
(* Registration of persistent tables as a global table and rollback *)

let init () = local_nametab := empty
let freeze () = !local_nametab
let unfreeze mc = local_nametab := mc

let _ = 
  Summary.declare_summary "local-names"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_section = false }

