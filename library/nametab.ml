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
open Nameops
open Declarations

(*s qualified names *)
type qualid = section_path

let make_qualid = make_path
let repr_qualid = repr_path

let string_of_qualid = string_of_path
let pr_qualid = pr_sp

let qualid_of_sp sp = sp
let make_short_qualid id = make_qualid empty_dirpath id
let qualid_of_dirpath dir = 
  let (l,a) = split_dirpath dir in
  make_qualid l a

exception GlobalizationError of qualid
exception GlobalizationConstantError of qualid

let error_global_not_found_loc loc q =
  Stdpp.raise_with_loc loc (GlobalizationError q)

let error_global_constant_not_found_loc loc q =
  Stdpp.raise_with_loc loc (GlobalizationConstantError q)

let error_global_not_found q = raise (GlobalizationError q)

(* Constructions and syntactic definitions live in the same space *)
type global_reference =
  | VarRef of variable
  | ConstRef of constant
  | IndRef of inductive
  | ConstructRef of constructor

type extended_global_reference =
  | TrueGlobal of global_reference
  | SyntacticDef of section_path

let sp_of_global env = function
  | VarRef id -> make_path empty_dirpath id
  | ConstRef sp -> sp
  | IndRef (sp,tyi) -> 
      (* Does not work with extracted inductive types when the first 
	 inductive is logic : if tyi=0 then basename sp else *)
      let mib = Environ.lookup_mind sp env in
      assert (tyi < mib.mind_ntypes && tyi >= 0);
      let mip = mib.mind_packets.(tyi) in
      let (p,_) = repr_path sp in
      make_path p mip.mind_typename
  | ConstructRef ((sp,tyi),i) ->
      let mib = Environ.lookup_mind sp env in
      assert (tyi < mib.mind_ntypes && i >= 0);
      let mip = mib.mind_packets.(tyi) in
      assert (i <= Array.length mip.mind_consnames && i > 0);
      let (p,_) = repr_path sp in
      make_path p mip.mind_consnames.(i-1)


(* Dictionaries of short names *)
type 'a nametree = ('a option * 'a nametree ModIdmap.t)
type ccitab = extended_global_reference nametree Idmap.t
type objtab = section_path nametree Idmap.t
type dirtab = dir_path nametree ModIdmap.t

let the_ccitab = ref (Idmap.empty : ccitab)
let the_libtab = ref (ModIdmap.empty : dirtab)
let the_sectab = ref (ModIdmap.empty : dirtab)
let the_objtab = ref (Idmap.empty : objtab)

let dirpath_of_reference ref =
  let sp = match ref with
    | ConstRef sp -> sp
    | VarRef id -> make_path empty_dirpath id
    | ConstructRef ((sp,_),_) -> sp
    | IndRef (sp,_) -> sp in
  let (p,_) = repr_path sp in
  p

let dirpath_of_extended_ref = function
  | TrueGlobal ref -> dirpath_of_reference ref
  | SyntacticDef sp ->
      let (p,_) = repr_path sp in p

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
  let extract = option_app (fun c -> repr_dirpath (extract_dirpath c)) in
  let rec push level (current,dirmap) = function
    | modid :: path as dir ->
	let mc = 
	  try ModIdmap.find modid dirmap
	  with Not_found -> (None, ModIdmap.empty)
	in
	let this =
          if level >= visibility then
            if extract current = Some dir then
              (* This is an absolute name, we must keep it otherwise it may
                 become unaccessible forever *)
              current
            else
              Some o
          else current in
	(this, ModIdmap.add modid (push (level+1) mc path) dirmap)
    | [] -> (Some o,dirmap) in
  push 0 tab (repr_dirpath dir)

let push_idtree extract_dirpath tab n dir id o =
  let modtab =
    try Idmap.find id !tab
    with Not_found -> (None, ModIdmap.empty) in
  tab := Idmap.add id (push_tree extract_dirpath modtab n dir o) !tab

let push_long_names_ccipath = push_idtree dirpath_of_extended_ref the_ccitab
let push_short_name_ccipath = push_idtree dirpath_of_extended_ref the_ccitab
let push_long_names_objpath =
  push_idtree (fun sp -> let (p,_) = repr_path sp in p) the_objtab
let push_short_name_objpath =
  push_idtree (fun sp -> let (p,_) = repr_path sp in p) the_objtab

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

let push_cci ~visibility:n sp ref =
  let dir, s = repr_path sp in
  (* We push partially qualified name (with at least one prefix) *)
  push_long_names_ccipath n dir s (TrueGlobal ref)

let push = push_cci

(* This is for Syntactic Definitions *)

let push_syntactic_definition sp =
  let dir, s = repr_path sp in
  push_long_names_ccipath 0 dir s (SyntacticDef sp)

let push_short_name_syntactic_definition sp =
  let _, s = repr_qualid (qualid_of_sp sp) in
  push_short_name_ccipath Pervasives.max_int empty_dirpath s (SyntacticDef sp)

(* This is for dischargeable non-cci objects (removed at the end of the
   section -- i.e. Hints, Grammar ...) *) (* --> Unused *)

let push_short_name_object sp =
  let _, s = repr_qualid (qualid_of_sp sp) in
  push_short_name_objpath 0 empty_dirpath s sp

(* This is for tactic definition names *)

let push_tactic_path sp =
  let dir, s = repr_qualid (qualid_of_sp sp) in
  push_long_names_objpath 0 dir s sp

(* This is to remember absolute Section/Module names and to avoid redundancy *)
let push_section fulldir =
  let dir, s = split_dirpath fulldir in
  (* We push all partially qualified name *)
  push_long_names_secpath dir s fulldir;
  push_long_names_secpath empty_dirpath s fulldir

(* These are entry points to locate names *)
let locate_in_tree tab dir =
  let dir = repr_dirpath dir in
  let rec search (current,modidtab) = function
    | modid :: path -> search (ModIdmap.find modid modidtab) path
    | [] -> match current with Some o -> o | _ -> raise Not_found
  in
  search tab dir

let locate_cci (qid:qualid) =
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

let locate_tactic qid =
  let (dir,id) = repr_qualid qid in
  locate_in_tree (Idmap.find id !the_objtab) dir

(* Actually, this table has only two levels, since only basename and *)
(* fullname are registered *)
let push_loaded_library fulldir =
  let dir, s = split_dirpath fulldir in
  push_long_names_libpath dir s fulldir;
  push_long_names_libpath empty_dirpath s fulldir

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
    | _ -> raise Not_found

let sp_of_id id = match locate_cci (make_short_qualid id) with
  | TrueGlobal ref -> ref
  | SyntacticDef _ ->
      anomaly ("sp_of_id: "^(string_of_id id)
	       ^" is not a true global reference but a syntactic definition")

let constant_sp_of_id id =
  match locate_cci (make_short_qualid id) with
    | TrueGlobal (ConstRef sp) -> sp
    | _ -> raise Not_found

let absolute_reference sp =
  let a = locate_cci sp in
  let (p,_) = repr_path sp in
  if not (dirpath_of_extended_ref a = p) then
    anomaly ("Not an absolute path: "^(string_of_path sp));
  match a with
    | TrueGlobal ref -> ref
    | _ -> raise Not_found

let locate_in_absolute_module dir id =
  absolute_reference (make_path dir id)

let global (loc,qid) =
  try match extended_locate qid with
    | TrueGlobal ref -> ref
    | SyntacticDef _ -> 
        user_err_loc (loc,"global",
          str "Unexpected reference to a syntactic definition: " ++
          pr_qualid qid)
  with Not_found ->
    error_global_not_found_loc loc qid

let exists_cci sp =
  try let _ = locate_cci sp in true
  with Not_found -> false

let exists_section dir =
  try let _ = locate_section (qualid_of_dirpath dir) in true
  with Not_found -> false


(* For a sp Coq.A.B.x, try to find the shortest among x, B.x, A.B.x
   and Coq.A.B.x is a qualid that denotes the same object. *)
let shortest_qualid_of_global env ref =  
  let sp = sp_of_global env ref in
  let (pth,id) = repr_path sp in
  let rec find_visible dir qdir =
    let qid = make_qualid qdir id in
    if (try locate qid = ref with Not_found -> false) then qid
    else match dir with
      | [] -> qualid_of_sp sp
      | a::l -> find_visible l (add_dirpath_prefix a qdir)
  in
  find_visible (repr_dirpath pth) (make_dirpath [])

let pr_global_env env ref =
  (* Il est important de laisser le let-in, car les streams s'évaluent
  paresseusement : il faut forcer l'évaluation pour capturer
  l'éventuelle levée d'une exception (le cas échoit dans le debugger) *)
  let s = string_of_qualid (shortest_qualid_of_global env ref) in
  (str s)

let global_inductive (loc,qid as locqid) =
  match global locqid with
  | IndRef ind -> ind
  | ref ->
      user_err_loc (loc,"global_inductive",
        pr_qualid qid ++ spc () ++ str "is not an inductive type")

(********************************************************************)

(********************************************************************)
(* Registration of tables as a global table and rollback            *)

type frozen = ccitab * dirtab * dirtab * objtab * identifier list

let init () = 
  the_ccitab := Idmap.empty; 
  the_libtab := ModIdmap.empty;
  the_sectab := ModIdmap.empty;
  the_objtab := Idmap.empty

let freeze () =
  !the_ccitab, 
  !the_libtab,
  !the_sectab,
  !the_objtab

let unfreeze (mc,ml,ms,mo) =
  the_ccitab := mc;
  the_libtab := ml;
  the_sectab := ms;
  the_objtab := mo

let _ = 
  Summary.declare_summary "names"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_section = false }
