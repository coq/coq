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
open Names
open Libobject
open Declarations
open Term

(*s qualified names *)
type qualid = dir_path * identifier

let make_qualid p id = (p,id)
let repr_qualid q = q

let string_of_qualid (l,id) =
  let dir = if l = [] then "" else string_of_dirpath l ^ "." in
  dir ^ string_of_id id
let pr_qualid p = pr_str (string_of_qualid p)

let qualid_of_sp sp = make_qualid (dirpath sp) (basename sp)
let qualid_of_dirpath dir = 
  let a,l = list_sep_last (repr_qualid dir) in
  make_qualid l a

exception GlobalizationError of qualid
exception GlobalizationConstantError of qualid

let error_global_not_found_loc loc q =
  Stdpp.raise_with_loc loc (GlobalizationError q)

let error_global_constant_not_found_loc loc q =
  Stdpp.raise_with_loc loc (GlobalizationConstantError q)

let error_global_not_found q = raise (GlobalizationError q)

(*s Roots of the space of absolute names *)

let coq_root = id_of_string "Coq"
let default_root_prefix = []

(* Obsolète
let roots = ref []
let push_library_root s = roots := list_add_set s !roots
*)
let push_library_root s = ()

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

let dirpath_of_reference = function
  | ConstRef sp -> dirpath sp
  | VarRef sp -> dirpath sp
  | ConstructRef ((sp,_),_) -> dirpath sp
  | IndRef (sp,_) -> dirpath sp

let dirpath_of_extended_ref = function
  | TrueGlobal ref -> dirpath_of_reference ref
  | SyntacticDef sp -> dirpath sp

(* How [visibility] works: a value of [0] means all suffixes of [dir] are
   allowed to access the object, a value of [1] means all suffixes, except the
   base name, are available, [2] means all suffixes except the base name and
   the name qualified by the module name *)

(* Concretely, library roots and directory are
   always open but modules/files are open only during their interactive
   construction or on demand if a precompiled one: for a name
   "Root.Rep.Lib.name", then "Lib.name", "Rep.Lib.name" and
   "Root.Rep.Lib.name", but not "name" are pushed; which means, visibility is
   always 1 *)

(* We add a binding of [[modid1;...;modidn;id]] to [o] in the name tab *)
(* We proceed in the reverse way, looking first to [id] *)
let push_tree extract_dirpath tab visibility dir o =
  let rec push level (current,dirmap) = function
    | modid :: path as dir ->
	let mc = 
	  try ModIdmap.find modid dirmap
	  with Not_found -> (None, ModIdmap.empty)
	in
	let this =
          if level >= visibility then
            if option_app extract_dirpath current = Some dir then
              (* This is an absolute name, we must keep it otherwise it may
                 become unaccessible forever *)
              current
            else
              Some o
          else current in
	(this, ModIdmap.add modid (push (level+1) mc path) dirmap)
    | [] -> (Some o,dirmap) in
  push 0 tab (List.rev dir)

let push_idtree extract_dirpath tab n dir id o =
  let modtab =
    try Idmap.find id !tab
    with Not_found -> (None, ModIdmap.empty) in
  tab := Idmap.add id (push_tree extract_dirpath modtab n dir o) !tab

let push_long_names_ccipath = push_idtree dirpath_of_extended_ref the_ccitab
let push_short_name_ccipath = push_idtree dirpath_of_extended_ref the_ccitab
let push_short_name_objpath = push_idtree dirpath the_objtab

let push_modidtree tab dir id o =
  let modtab =
    try ModIdmap.find id !tab
    with Not_found -> (None, ModIdmap.empty) in
  tab := ModIdmap.add id (push_tree (fun x -> x) modtab 0 dir o) !tab

let push_long_names_secpath = push_modidtree the_sectab
let push_long_names_libpath = push_modidtree the_libtab

(* These are entry points for new declarations at toplevel *)

(* This is for permanent constructions (never discharged -- but with
   possibly limited visibility, i.e. Theorem, Lemma, Definition, Axiom,
   Parameter but also Remark and Fact) *)

let push_cci n sp ref =
  let dir, s = repr_qualid (qualid_of_sp sp) in
  (* We push partially qualified name (with at least one prefix) *)
  push_long_names_ccipath n dir s (TrueGlobal ref)

let push = push_cci

(* This is for Syntactic Definitions *)

let push_syntactic_definition sp =
  let dir, s = repr_qualid (qualid_of_sp sp) in
  push_long_names_ccipath 0 dir s (SyntacticDef sp)

let push_short_name_syntactic_definition sp =
  let _, s = repr_qualid (qualid_of_sp sp) in
  push_short_name_ccipath Pervasives.max_int [] s (SyntacticDef sp)

(* This is for dischargeable non-cci objects (removed at the end of the
   section -- i.e. Hints, Grammar ...) *) (* --> Unused *)

let push_short_name_object sp =
  let _, s = repr_qualid (qualid_of_sp sp) in
  push_short_name_objpath 0 [] s sp

(* This is to remember absolute Section/Module names and to avoid redundancy *)

let push_section fulldir =
  let dir, s = split_dirpath fulldir in
  (* We push all partially qualified name *)
  push_long_names_secpath dir s fulldir;
  push_long_names_secpath [] s fulldir

(* These are entry points to locate names *)
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
  (* TODO: restrict to defined constants *)
  match locate_cci qid with
    | TrueGlobal (ConstRef sp) -> sp
    | TrueGlobal (VarRef sp) -> sp
    | _ -> raise Not_found

let sp_of_id _ id = match locate_cci (make_qualid [] id) with
  | TrueGlobal ref -> ref
  | SyntacticDef _ ->
      anomaly ("sp_of_id: "^(string_of_id id)
	       ^" is not a true global reference but a syntactic definition")

let constant_sp_of_id id =
  match locate_cci (make_qualid [] id) with
    | TrueGlobal (ConstRef sp) -> sp
    | _ -> raise Not_found

let absolute_reference sp =
  let a = locate_cci (qualid_of_sp sp) in
  if not (dirpath_of_extended_ref a = dirpath sp) then
    anomaly ("Not an absolute path: "^(string_of_path sp));
  match a with
    | TrueGlobal ref -> ref
    | _ -> raise Not_found

let locate_in_absolute_module dir id =
  absolute_reference (make_path dir id CCI)

let global loc qid =
  try match extended_locate qid with
    | TrueGlobal ref -> ref
    | SyntacticDef _ -> 
        error
          ("Unexpected reference to a syntactic definition: "
           ^(string_of_qualid qid))
  with Not_found ->
    error_global_not_found_loc loc qid

let exists_cci sp =
  try let _ = locate_cci (qualid_of_sp sp) in true
  with Not_found -> false

let exists_section dir =
  try let _ = locate_section (qualid_of_dirpath dir) in true
  with Not_found -> false

(********************************************************************)

(********************************************************************)
(* Registration of tables as a global table and rollback            *)

type frozen = ccitab * dirtab * dirtab * objtab * identifier list

let init () = 
  the_ccitab := Idmap.empty; 
  the_libtab := ModIdmap.empty;
  the_sectab := ModIdmap.empty;
  the_objtab := Idmap.empty
(*  ;roots := []*)

let freeze () =
  !the_ccitab, 
  !the_libtab,
  !the_sectab,
  !the_objtab
(*  ,!roots*)

let unfreeze (mc,ml,ms,mo(*,r*)) =
  the_ccitab := mc;
  the_libtab := ml;
  the_sectab := ms;
  the_objtab := mo(*;
  roots := r*)

let _ = 
  Summary.declare_summary "names"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_section = false }
