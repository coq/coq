(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Libobject
open Summary

type node = 
  | Leaf of obj
  | Module of dir_path
  | OpenedSection of module_ident * Summary.frozen
  (* bool is to tell if the section must be opened automatically *)
  | ClosedSection of bool * module_ident * library_segment
  | FrozenState of Summary.frozen

and library_entry = section_path * node

and library_segment = library_entry list


(* We keep trace of operations in the stack [lib_stk]. 
   [path_prefix] is the current path of sections, where sections are stored in 
   ``correct'' order, the oldest coming first in the list. It may seems 
   costly, but in practice there is not so many openings and closings of
   sections, but on the contrary there are many constructions of section
   paths based on the library path. *) 

let lib_stk = ref ([] : (section_path * node) list)

let default_module = make_dirpath [id_of_string "Scratch"]
let module_name = ref None
let path_prefix = ref (default_module : dir_path)

let module_sp () =
  match !module_name with Some m -> m | None -> default_module

let recalc_path_prefix () =
  let rec recalc = function
    | (sp, OpenedSection (modid,_)) :: _ -> (dirpath sp)@[modid]
    | _::l -> recalc l
    | [] -> module_sp ()
  in
  path_prefix := recalc !lib_stk

let pop_path_prefix () =
  let rec pop = function
    | [] -> assert false
    | [_] -> []
    | s::l -> s :: (pop l)
  in
  path_prefix := pop !path_prefix

let make_path id k = Names.make_path !path_prefix id k

let cwd () = !path_prefix

let find_entry_p p = 
  let rec find = function
    | [] -> raise Not_found
    | ent::l -> if p ent then ent else find l
  in
  find !lib_stk

let split_lib sp = 
  let rec findrec after = function
    | ((sp',obj) as hd)::before ->
      	if sp = sp' then (after,hd,before) else findrec (hd::after) before
    | [] -> error "no such entry"
  in 
  findrec [] !lib_stk

(* Adding operations. *)

let add_entry sp node =
  lib_stk := (sp,node) :: !lib_stk

let anonymous_id = 
  let n = ref 0 in
  fun () -> incr n; id_of_string ("_" ^ (string_of_int !n))

let add_anonymous_entry node =
  let sp = make_path (anonymous_id()) OBJ in
  add_entry sp node;
  sp

let add_leaf id kind obj =
  let sp = make_path id kind in
  cache_object (sp,obj);
  add_entry sp (Leaf obj);
  sp

let add_anonymous_leaf obj =
  let sp = make_path (anonymous_id()) OBJ in
  cache_object (sp,obj);
  add_entry sp (Leaf obj)

let add_frozen_state () =
  let _ = add_anonymous_entry (FrozenState (freeze_summaries())) in ()

let contents_after = function
  | None -> !lib_stk
  | Some sp -> let (after,_,_) = split_lib sp in after

(* Sections. *)

let open_section id =
  let dir = !path_prefix @ [id] in
  let sp = make_path id OBJ in
  if Nametab.exists_section dir then
    errorlabstrm "open_section" [< pr_id id; 'sTR " already exists" >];
  add_entry sp (OpenedSection (id, freeze_summaries()));
  path_prefix := dir;
  sp

let check_for_module () =
  let is_decl = function (_,FrozenState _) -> false | _ -> true in
  try
    let _ = find_entry_p is_decl in
    error "a module can not be started after some declarations"
  with Not_found -> ()

let start_module s =
  if !module_name <> None then
    error "a module is already started";
  if !path_prefix <> default_module then
    error "some sections are already opened";
  module_name := Some s;
  (match split_dirpath s with [],id -> Nametab.push_library_root id | _ -> ());
  Univ.set_module s;
  let _ = add_anonymous_entry (Module s) in
  path_prefix := s

let end_module s =
  match !module_name with
    | None -> error "no module declared"
    | Some m ->
	let bm = snd (split_dirpath m) in
	if bm <> s then
	  error ("The current open module has basename "^(string_of_id bm));
	m

let is_opened_section = function (_,OpenedSection _) -> true | _ -> false

let sections_are_opened () =
  try let _ = find_entry_p is_opened_section in true
  with Not_found -> false

let export_segment seg =
  let rec clean acc = function
    | (_,Module _) :: _ | [] -> acc
    | (sp,Leaf o) as node :: stk -> 
	(match export_object o with 
	   | None -> clean acc stk
	   | Some o' -> clean ((sp,Leaf o') :: acc) stk)
    | (sp,ClosedSection _ as item) :: stk -> clean (item :: acc) stk
    | (_,OpenedSection _) :: _ -> error "there are still opened sections"
    | (_,FrozenState _) :: stk -> clean acc stk
  in
  clean [] seg

let close_section export id =
  let sp,fs = 
    try match find_entry_p is_opened_section with
      | sp,OpenedSection (id',fs) -> 
	  if id<>id' then error "this is not the last opened section"; (sp,fs)
      | _ -> assert false
    with Not_found ->
      error "no opened section"
  in
  let (after,_,before) = split_lib sp in
  lib_stk := before;
  let after' = export_segment after in
  pop_path_prefix ();
  add_entry (make_path id OBJ) (ClosedSection (export, id, after'));
  (sp,after,fs)

(* The following function exports the whole library segment, that will be 
   saved as a module. Objects are presented in chronological order, and
   frozen states are removed. *)

let export_module s =
  export_segment !lib_stk

(* Backtracking. *)

let recache_decl = function
  | (sp, Leaf o) -> cache_object (sp,o)
  | _ -> ()

let recache_context ctx =
  List.iter recache_decl ctx

let is_frozen_state = function (_,FrozenState _) -> true | _ -> false

let reset_to sp =
  let (_,_,before) = split_lib sp in
  lib_stk := before;
  recalc_path_prefix ();
  let spf = match find_entry_p is_frozen_state with
    | (sp, FrozenState f) -> unfreeze_summaries f; sp
    | _ -> assert false
  in
  let (after,_,_) = split_lib spf in
  recache_context after

let reset_name id =
  let (sp,_) = 
    try
      find_entry_p (fun (sp,_) -> id = basename sp)
    with Not_found ->
      error (string_of_id id ^ ": no such entry")
  in
  reset_to sp

(* [dir] is a section dir if [module] < [dir] <= [path_prefix] *)
let is_section_p sp =
  not (is_dirpath_prefix_of sp (module_sp ()))
  & (is_dirpath_prefix_of sp !path_prefix)

(* State and initialization. *)

type frozen = dir_path option * library_segment

let freeze () = (!module_name, !lib_stk)

let unfreeze (mn,stk) =
  module_name := mn;
  lib_stk := stk;
  recalc_path_prefix ()

let init () =
  lib_stk := [];
  add_frozen_state ();
  module_name := None;
  path_prefix := [];
  init_summaries()

(* Initial state. *)

let initial_state = ref (None : section_path option)

let declare_initial_state () = 
  let sp = add_anonymous_entry (FrozenState (freeze_summaries())) in
  initial_state := Some sp

let reset_initial () =
  match !initial_state with
    | None -> init ()
    | Some sp -> 
  	begin match split_lib sp with
	  | (_,(_,FrozenState fs as hd),before) ->
	      lib_stk := hd::before;
	      recalc_path_prefix ();
	      unfreeze_summaries fs
	  | _ -> assert false
	end


