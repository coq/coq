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
open Nameops
open Libnames
open Nametab
open Table
open Miniml
open Mlutil
open Ocaml

module Orefset = struct 
  type t = { set : Refset.t ; list : global_reference list }
  let empty = { set = Refset.empty ; list = [] }
  let add r o = 
    if Refset.mem r o.set then o 
    else { set = Refset.add r o.set ; list = r :: o.list }
  let set o = o.set
  let list o = o.list
end

type updown = { mutable up : Orefset.t ; mutable down : Orefset.t }

let add_down o r = o.down <- Orefset.add r o.down
let add_up o r = o.up <- Orefset.add r o.up
let lang_add_type o r = if lang () = Haskell then add_up o r else add_down o r

(*s Get all references used in one [ml_decl] list. *)

let mltype_get_references o t = 
  let rec get_rec = function 
    | Tglob (r,l) -> lang_add_type o r; List.iter get_rec l 
    | Tarr (a,b) -> get_rec a; get_rec b 
    | _ -> () 
  in get_rec t

let ast_get_references o a = 
  let rec get_rec a =
    ast_iter get_rec a;
    match a with 
      | MLglob r -> add_down o r
      | MLcons (r,_) -> add_up o r
      | MLcase (_,v) as a -> Array.iter (fun (r,_,_) -> add_up o r) v
      | MLcast (_,t) -> mltype_get_references o t 
      | _ -> ()
  in get_rec a

let ip_of_indref = function 
  | IndRef ip -> ip 
  | _ -> assert false

let decl_get_references ld = 
  let o = { up = Orefset.empty ; down = Orefset.empty } in 
  let one_decl = function 
    | Dind (l,_) -> 
	List.iter (fun (_,r,l) -> 
		     lang_add_type o r; 
		     (try 
			List.iter (add_down o) (find_proj (ip_of_indref r))
		      with Not_found -> ()); 
		     List.iter (fun (r,l) -> 
				  add_up o r; 
				  List.iter (mltype_get_references o) l) l) l
    | Dtype (r,_,t) -> lang_add_type o r; mltype_get_references o t 
    | Dterm (r,a,t) -> 
	add_down o r; ast_get_references o a; mltype_get_references o t
    | Dfix(rv,c,t) -> 
	Array.iter (add_down o) rv; 
	Array.iter (ast_get_references o) c; 
	Array.iter (mltype_get_references o) t
    | DcustomTerm (r,_) -> add_down o r
    | DcustomType (r,_) -> lang_add_type o r
  in 
  List.iter one_decl ld; 
  o

(*S Modules considerations. *)

let long_module r = 
  match modpath (kn_of_r r) with 
    | MPfile d -> d
    | _ -> anomaly "TODO: extraction not ready for true modules"

let short_module r = List.hd (repr_dirpath (long_module r))

(*s [extract_module m] returns all the global reference declared 
  in a module. This is done by traversing the segment of module [m]. 
  We just keep constants and inductives. *)

let segment_contents seg = 
  let get_reference = function
    | (_,kn), Lib.Leaf o ->
	(match Libobject.object_tag o with
	   | "CONSTANT" -> ConstRef kn
	   | "INDUCTIVE" -> IndRef (kn,0)
	   | _ -> failwith "caught")
    | _ -> failwith "caught"
  in
  Util.map_succeed get_reference seg

let module_contents m =
  segment_contents (Declaremods.module_objects (MPfile m))

(*s The next function finds all names common to at least two used modules. *)

let modules_reference_clashes modules = 
  let id_of_r r = lowercase_id (id_of_global None r) in
  let map = 
    Dirset.fold
      (fun mod_name map -> 
	 let rl = List.map id_of_r (module_contents mod_name) in 
	 List.fold_left (fun m id -> Idmap.add id (Idmap.mem id m) m) map rl)
      modules Idmap.empty 
  in Idmap.fold (fun i b s -> if b then Idset.add i s else s) map Idset.empty

(*S Renamings. *)

(*s Tables of global renamings *)

let keywords = ref Idset.empty
let global_ids = ref Idset.empty

let renamings = Hashtbl.create 97
let rename r s = Hashtbl.add renamings r s
let get_renamings r = Hashtbl.find renamings r 

let create_mono_renamings decls =  
  let { up = u ; down = d } = decl_get_references decls in 
  let add upper r = 
    try if not (to_inline r) then raise Not_found; 
      rename r (find_ml_extraction r)  
    with Not_found -> 
      let id = id_of_global None r in 
      let id = if upper then uppercase_id id else lowercase_id id in
      let id = rename_id id !global_ids in 
      global_ids := Idset.add id !global_ids; 
      rename r (string_of_id id)
  in 
  List.iter (add true) (List.rev (Orefset.list u)); 
  List.iter (add false) (List.rev (Orefset.list d))

let create_modular_renamings current_module decls = 
  let { up = u ; down = d } = decl_get_references decls in 
  let modules = 
    let f r s = Dirset.add (long_module r) s in 
    Refset.fold f (Orefset.set u) (Refset.fold f (Orefset.set d) Dirset.empty)
  in 
  let modular_clashs = modules_reference_clashes modules 
  in 
  let clash r id = 
    exists_cci (make_path (dirpath (sp_of_global None r)) id)
  in 
  let prefix upper r id = 
    let prefix = if upper then "Coq_" else "coq_" in 
    let id' = if upper then uppercase_id id else lowercase_id id in
    if (Idset.mem id' !keywords) || (id <> id' && clash r id') then 
      id_of_string (prefix^(string_of_id id))
    else id'
  in
  let add upper r = 
    try if not (to_inline r) then raise Not_found; 
      rename r (find_ml_extraction r)  
    with Not_found -> 
      let id = id_of_global None r in 
      let m = short_module r in 
      let id' = prefix upper r id in 
      let qualify = 
	(m <> current_module) && (Idset.mem (lowercase_id id) modular_clashs) 
      in 
      if qualify then 
	let s = String.capitalize (string_of_id m) ^ "." ^ (string_of_id id') in
	Hashtbl.add renamings r s
      else begin
	global_ids := Idset.add id' !global_ids;
	Hashtbl.add renamings r (string_of_id id')
      end
  in
  List.iter (add true) (List.rev (Orefset.list u)); 
  List.iter (add false) (List.rev (Orefset.list d)); 
  Idset.remove current_module 
    (Dirset.fold (fun m s -> Idset.add (List.hd (repr_dirpath m)) s) 
       modules Idset.empty)
		    
(*s Renaming issues at toplevel *)

module ToplevelParams = struct
  let globals () = Idset.empty
  let pp_global r = Printer.pr_global r
end

(*s Renaming issues for a monolithic or modular extraction. *)

module StdParams = struct
  let globals () = !global_ids
  let pp_global r = str (Hashtbl.find renamings r)
end

module ToplevelPp = Ocaml.Make(ToplevelParams)
module OcamlPp = Ocaml.Make(StdParams)
module HaskellPp = Haskell.Make(StdParams)
module SchemePp = Scheme.Make(StdParams)

let pp_decl () = match lang () with 
  | Ocaml -> OcamlPp.pp_decl
  | Haskell -> HaskellPp.pp_decl
  | Scheme -> SchemePp.pp_decl
  | Toplevel -> ToplevelPp.pp_decl

let set_keywords () =
  (match lang () with 
    | Ocaml -> keywords := Ocaml.keywords
    | Haskell -> keywords := Haskell.keywords
    | Scheme -> keywords := Scheme.keywords
    | Toplevel -> keywords := Idset.empty);
  global_ids := !keywords
    
let preamble prm = match lang () with 
  | Ocaml -> Ocaml.preamble prm   
  | Haskell -> Haskell.preamble prm
  | Scheme -> Scheme.preamble prm
  | Toplevel -> (fun _ _ -> mt ())
	
let pp_comment s = match lang () with 
  | Haskell -> str "-- " ++ s ++ fnl () 
  | Scheme -> str ";" ++ s ++ fnl () 
  | Ocaml | Toplevel -> str "(* " ++ s ++ str " *)" ++ fnl ()

let pp_logical_ind r = 
  pp_comment (Printer.pr_global r ++ str " : logical inductive")

let pp_singleton_ind r = 
  pp_comment (Printer.pr_global r ++ str " : singleton inductive constructor")

(*S Extraction to a file. *)

let extract_to_file f prm decls =
  cons_cofix := Refset.empty;
  Hashtbl.clear renamings;
  set_keywords ();
  let used_modules = 
    if lang () = Toplevel then Idset.empty 
    else if prm.modular then
      create_modular_renamings prm.mod_name decls
    else begin create_mono_renamings decls; Idset.empty end
  in 
  let pp_decl = pp_decl () in 
  let cout = match f with 
    | None -> stdout
    | Some f -> open_out f in
  let ft = Pp_control.with_output_to cout in
  let print_dummys = 
    (decl_search MLdummy decls, 
     decl_type_search Tdummy decls, 
     decl_type_search Tunknown decls) in 
  pp_with ft (preamble prm used_modules print_dummys);
  if not prm.modular then begin 
    List.iter (fun r -> pp_with ft (pp_logical_ind r)) 
      (List.filter Extraction.decl_is_logical_ind prm.to_appear); 
    List.iter (fun r -> pp_with ft (pp_singleton_ind r)) 
      (List.filter Extraction.decl_is_singleton prm.to_appear); 
  end;
  begin try
    List.iter (fun d -> msgnl_with ft (pp_decl d)) decls
  with e ->
    pp_flush_with ft (); if f <> None then close_out cout; raise e
  end;
  pp_flush_with ft ();
  if f <> None then close_out cout;  
    
(*i 
  (* DO NOT REMOVE: used when making names resolution *)
  let cout = open_out (f^".ren") in 
  let ft = Pp_control.with_output_to cout in
  Hashtbl.iter 
    (fun r id -> 
       if short_module r = !current_module then 
	 msgnl_with ft (pr_id id ++ str " " ++ pr_sp (sp_of_r r)))
    renamings;
  pp_flush_with ft ();
  close_out cout;
i*)    







