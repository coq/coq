
(* $Id$ *)

open Util
open Names
open Libobject
open Summary

type node = 
  | Leaf of obj
  | OpenedSection of string
  | ClosedSection of string * library_segment
  | FrozenState of Summary.frozen

and library_segment = (section_path * node) list

type library_entry = section_path * node


(* We keep trace of operations in the stack [lib_stk]. 
   [path_prefix] is the current path of sections, where sections are stored in 
   ``correct'' order, the oldest coming first in the list. It may seems 
   costly, but in practice there is not so many openings and closings of
   sections, but on the contrary there are many constructions of section
   paths based on the library path. *) 

let lib_stk = ref ([] : (section_path * node) list)

let module_name = ref None
let path_prefix = ref ([] : string list)

let recalc_path_prefix () =
  let rec recalc = function
    | (sp, OpenedSection _) :: _ ->
	let (pl,id,_) = repr_path sp in pl@[string_of_id id]
    | _::l -> recalc l
    | [] -> (match !module_name with Some m -> [m] | None -> [])
  in
  path_prefix := recalc !lib_stk

let pop_path_prefix () =
  let rec pop acc = function
    | [] -> assert false
    | [_] -> path_prefix := acc
    | s::l -> pop (s::acc) l
  in
  pop [] !path_prefix

let make_path id k = Names.make_path !path_prefix id k

let cwd () = !path_prefix

let find_entry_p p = 
  let rec find = function
    | [] -> raise Not_found
    | ent::l -> if p ent then ent else find l
  in
  find !lib_stk

let split_lib sp = 
  let rec findrec acc = function
    | ((sp',obj) as hd)::t ->
      	if sp = sp' then (acc,hd,t) else findrec (hd::acc) t
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
  add_entry sp node

let add_leaf id kind obj =
  let sp = make_path id kind in
  add_entry sp (Leaf obj);
  sp

let add_anonymous_leaf obj =
  add_anonymous_entry (Leaf obj)

let add_frozen_state () =
  add_anonymous_entry (FrozenState (freeze_summaries()))

let contents_after = function
  | None -> !lib_stk
  | Some sp -> let (after,_,_) = split_lib sp in after


(* Sections. *)

let open_section s =
  let sp = make_path (id_of_string s) OBJ in
  add_entry sp (OpenedSection s);
  path_prefix := !path_prefix @ [s];
  sp

let check_for_module () =
  let is_decl = function (_,FrozenState _) -> false | _ -> true in
  try
    let _ = find_entry_p is_decl in
    error "a module can not be opened after some declarations"
  with Not_found -> ()

let open_module s =
  if !module_name <> None then error "a module is already opened";
  check_for_module ();
  module_name := Some s

let is_opened_section = function (_,OpenedSection _) -> true | _ -> false

let close_section s =
  let sp = 
    try match find_entry_p is_opened_section with
      | sp,OpenedSection s' -> 
	  if s <> s' then error "this is not the last opened section"; sp
      | _ -> assert false
    with Not_found ->
      error "no opened section"
  in
  let (after,_,before) = split_lib sp in
  lib_stk := before;
  add_entry sp (ClosedSection (s,after));
  add_frozen_state ();
  pop_path_prefix ()

(* The following function exports the whole library segment, that will be 
   saved as a module. Objects are presented in chronological order, and
   closed sections and frozen states are removed. *)

let export_module () =
  if !module_name = None then error "no module declared";
  let rec export acc = function
    | [] -> acc
    | (_,Leaf _) as node :: stk -> export (node::acc) stk
    | (_,OpenedSection _) :: _ -> error "there are still opened sections"
    | (_,(FrozenState _ | ClosedSection _)) :: stk -> export acc stk
  in
  export [] !lib_stk


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
  let (spf,frozen) = match find_entry_p is_frozen_state with
    | (sp, FrozenState f) -> sp,f
    | _ -> assert false
  in
  unfreeze_summaries frozen;
  let (after,_,_) = split_lib spf in
  recache_context (List.rev after)


(* State and initialization. *)

type frozen = library_segment

let freeze () = !lib_stk

let unfreeze stk =
  lib_stk := stk;
  recalc_path_prefix ()

let init () =
  lib_stk := [];
  add_frozen_state ();
  path_prefix := []

