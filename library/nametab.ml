(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Pp
open Identifier
open Names
open Declarations
open Term
open Libnames
open Libobject

exception GlobalizationError of qualid

let error_global_not_found_loc loc q =
  Stdpp.raise_with_loc loc (GlobalizationError q)

let error_global_not_found q = raise (GlobalizationError q)

(*s Roots of the space of absolute names *)

let roots = ref []
let push_library_root s = 
  roots := list_add_set s !roots

let coq_root = id_of_string "Coq"
let default_root_prefix = [(id_of_string "Scratch")]

(* Constructions and syntactic definitions live in the same space *)
type extended_global_reference =
  | TrueGlobal of global_reference
  | SyntacticDef of section_path

type 'a nametree = ('a option * 'a nametree ModIdmap.t)
type ccitab = extended_global_reference nametree Idmap.t
type objtab = section_path nametree Idmap.t
type dirtab = dir_path nametree ModIdmap.t

let the_ccitab = ref (Idmap.empty : ccitab)
let the_libtab = ref (ModIdmap.empty : dirtab)
let the_sectab = ref (ModIdmap.empty : dirtab)
let the_objtab = ref (Idmap.empty : objtab)


(* This table will translate global_references back to section paths *)
module Globtab = Map.Make(struct type t=global_reference 
				 let compare = compare end)

type globtab = qualid Globtab.t

let the_globtab = ref (Globtab.empty : globtab)

(* How necessarily_open works: concretely, roots and directory are
   always open but libraries are open only during their interactive
   construction or on demand if a precompiled one; then for a name
   "Root.Rep.Lib.name", then "Lib.name", "Rep.Lib.name" and
   "Root.Rep.Lib.name", but not "name" are pushed *)

(* We add a binding of [[modid1;...;modidn;id]] to [o] in the name tab *)
(* We proceed in the reverse way, looking first to [id] *)
let push_tree tab dir o =
  let rec push necessarily_open (current,dirmap) = function
    | modid :: path as dir ->
	let mc = 
	  try ModIdmap.find modid dirmap
	  with Not_found -> (None, ModIdmap.empty)
	in
	let this = if necessarily_open then Some o else current in
	(this, ModIdmap.add modid (push true mc path) dirmap)
    | [] -> (Some o,dirmap) in
  push false tab (List.rev dir)

let push_idtree tab dir id o =
  let modtab =
    try Idmap.find id !tab
    with Not_found -> (None, ModIdmap.empty) in
  tab := Idmap.add id (push_tree modtab dir o) !tab

let push_long_names_ccipath = push_idtree the_ccitab
let push_short_name_ccipath = push_idtree the_ccitab
let push_short_name_objpath = push_idtree the_objtab

let push_modidtree tab dir id o =
  let modtab =
    try ModIdmap.find id !tab
    with Not_found -> (None, ModIdmap.empty) in
  tab := ModIdmap.add id (push_tree modtab dir o) !tab

let push_long_names_secpath = push_modidtree the_sectab
let push_long_names_libpath = push_modidtree the_libtab

(* These are entry points for new declarations at toplevel *)

(* This is for permanent constructions (never discharged -- but with
   possibly limited visibility, i.e. Theorem, Lemma, Definition, Axiom,
   Parameter but also Remark and Fact) *)

let push_cci sp ref =
  let dir, s = repr_qualid (qualid_of_sp sp) in
  (* We push partially qualified name (with at least one prefix) *)
  push_long_names_ccipath dir s (TrueGlobal ref);
  the_globtab := Globtab.add ref (qualid_of_sp sp) !the_globtab

let push = push_cci

let push_short_name id ref =
  (* We push a volatile unqualified name *)
  push_short_name_ccipath [] id (TrueGlobal ref);
  match ref with
    | VarRef id -> 
	the_globtab := Globtab.add ref (make_qualid [] id) !the_globtab
    | _ -> ()
(* This is for Syntactic Definitions *)

let push_syntactic_definition sp =
  let dir, s = repr_qualid (qualid_of_sp sp) in
  push_long_names_ccipath dir s (SyntacticDef sp)

let push_short_name_syntactic_definition sp =
  let _, s = repr_qualid (qualid_of_sp sp) in
  push_short_name_ccipath [] s (SyntacticDef sp)

(* This is for dischargeable non-cci objects (removed at the end of the
   section -- i.e. Hints, Grammar ...) *) (* --> Unused *)

let push_short_name_object sp =
  push_short_name_objpath [] (basename sp) sp

(* This is to remember absolute Section/Module names and to avoid redundancy *)

let push_section fulldir =
  let dir, s = split_dirpath fulldir in
  (* We push all partially qualified name *)
  push_long_names_secpath dir s fulldir;
  push_long_names_secpath [] s fulldir

(* These are entry points to locate names *)
(* If the name starts with the coq_root name, then it is an absolute name *)
let locate_in_tree tab dir =
  let dir = List.rev dir in
  let rec search (current,modidtab) = function
    | modid :: path -> search (ModIdmap.find modid modidtab) path
    | [] -> match current with Some o -> o | _ -> raise Not_found
  in
  search tab dir

let locate_cci qid =
  let (dir,id) = repr_qualid qid in
  locate_in_tree (Idmap.find id !the_ccitab) dir

(* This should be used when syntactic definitions are allowed *)
let extended_locate = locate_cci

(* This should be used when no syntactic definitions is expected *)
let locate qid = match locate_cci qid with
  | TrueGlobal ref -> ref
  | SyntacticDef _ -> raise Not_found

let locate_obj qid =
  let (dir,id) = repr_qualid qid in
  locate_in_tree (Idmap.find id !the_objtab) dir

(* Actually, this table has only two levels, since only basename and *)
(* fullname are registered *)
let push_loaded_library fulldir =
  let dir, s = split_dirpath fulldir in
  push_long_names_libpath dir s fulldir;
  push_long_names_libpath [] s fulldir

let locate_loaded_library qid =
  let (dir,id) = repr_qualid qid in
  locate_in_tree (ModIdmap.find id !the_libtab) dir

let locate_section qid =
  let (dir,id) = repr_qualid qid in
  locate_in_tree (ModIdmap.find id !the_sectab) dir

(* Derived functions *)

let locate_constant qid =
  match locate_cci qid with
    | TrueGlobal (ConstRef ln) -> ln
    | _ -> raise Not_found

let locate_mind qid =
  match locate_cci qid with
    | TrueGlobal (IndRef (ln,_)) -> ln
    | _ -> raise Not_found

let sp_of_id _ id = match locate_cci (make_qualid [] id) with
  | TrueGlobal ref -> ref
  | SyntacticDef _ ->
      anomaly ("sp_of_id: "^(string_of_id id)
	       ^" is not a true global reference but a syntactic definition")

let check_absoluteness dir =
  match dir with
    | a::_ when List.mem a !roots -> ()
    | _ -> anomaly ("Not an absolute dirpath: "^(string_of_dirpath dir))

let is_absolute_dirpath = function
    | a::_ when List.mem a !roots -> true
    | _ -> false

let absolute_reference sp =
  check_absoluteness (dirpath sp);
  locate (qualid_of_sp sp)

let locate_in_absolute_module dir id =
  check_absoluteness dir;
  locate (make_qualid dir id)

(*
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
*)
let exists_cci sp =
  try let _ = locate_cci (qualid_of_sp sp) in true
  with Not_found -> false

let exists_section dir =
  try let _ = locate_section (qualid_of_dirpath dir) in true
  with Not_found -> false


let get_full_qualid ref = Globtab.find ref !the_globtab

let get_ident ref = snd (repr_qualid (get_full_qualid ref))

let get_short_qualid ref = 
  let full_qid = get_full_qualid ref in
  let dir,id = repr_qualid full_qid in
  let rec find_visible dir qdir =
    let qid = make_qualid qdir id in
    if (try locate qid = ref with Not_found -> false) then qid
    else match dir with
      | [] -> full_qid
      | a::l -> find_visible l (a::qdir)
  in
  find_visible (List.rev dir) []


(********************************************************************)
(* Registration of tables as a global table and rollback            *)

type frozen = ccitab * dirtab * dirtab * objtab * globtab * identifier list

let init () = 
  the_ccitab := Idmap.empty; 
  the_libtab := ModIdmap.empty;
  the_sectab := ModIdmap.empty;
  the_objtab := Idmap.empty;
  the_globtab := Globtab.empty;
  roots := []

let freeze () =
  !the_ccitab, 
  !the_libtab,
  !the_sectab,
  !the_objtab,
  !the_globtab,
  !roots

let unfreeze (mc,ml,ms,mo,gt,r) =
  the_ccitab := mc;
  the_libtab := ml;
  the_sectab := ms;
  the_objtab := mo;
  the_globtab := gt;
  roots := r

let _ = 
  Summary.declare_summary "names"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_section = false }

