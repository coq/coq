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
open Term
open Declarations
open Nameops
open Libnames
open Table
open Miniml
open Mlutil
open Ocaml

(*s Get all references used in one [ml_structure]. *)

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

let struct_get_references struc = 
  let o = { up = Orefset.empty ; down = Orefset.empty } in 
  let do_term r = o.down <- Orefset.add (long_r r) o.down in
  let do_cons r = o.up <- Orefset.add (long_r r) o.up in 
  let do_type = if lang () = Haskell then do_cons else do_term in 
  struct_iter_references do_term do_cons do_type struc; o

(*S Renamings. *)

(*s Tables of global renamings *)

let keywords = ref Idset.empty
let global_ids = ref Idset.empty
let modular = ref false

let renamings = Hashtbl.create 97
let rename r s = Hashtbl.add renamings r s
let get_renamings r = Hashtbl.find renamings r 

let must_qualify = ref Refset.empty

let is_upper s = match s.[0] with 'A' .. 'Z' -> true | _ -> false

let is_lower s = match s.[0] with 'a' .. 'z' | '_' -> true | _ -> false

let modular_rename up id = 
  let s = string_of_id id in
  let prefix = if up then "Coq_" else "coq_" in 
  let check = if up then is_upper else is_lower in 
  if not (check s) ||
    (Idset.mem id !keywords) ||
    (String.length s >= 4 && String.sub s 0 4 = prefix) 
  then prefix ^ s
  else s

let rename_module = modular_rename true 

let mp_to_list mp = 
  let rec f ls = function 
    | MPfile d -> 
	String.capitalize (string_of_id (List.hd (repr_dirpath d))) :: ls
    | MPself msid -> rename_module (id_of_msid msid) :: ls
    | MPbound mbid -> rename_module (id_of_mbid mbid) :: ls
    | MPdot (mp,l) -> f (rename_module (id_of_label l) :: ls) mp
  in f [] mp

let mp_to_list' mp = 
  let rec f ls = function 
    | mp when at_toplevel mp -> ls
    | MPself msid -> rename_module (id_of_msid msid) :: ls
    | MPbound mbid -> rename_module (id_of_mbid mbid) :: ls
    | MPdot (mp,l) -> f (rename_module (id_of_label l) :: ls) mp
    | _ -> assert false
  in f [] mp

let string_of_modlist l = 
  List.fold_right (fun s s' -> if s' = "" then s else s ^ "." ^ s') l ""

let string_of_ren l s = 
  if l = [] then s else (string_of_modlist l)^"."^s

let contents_first_level mp = 
  let s = ref Stringset.empty in 
  let add b id = s := Stringset.add (modular_rename b id) !s in 
  let upper_type = (lang () = Haskell) in
  let contents_seb = function 
    | (l, SEBconst cb) -> 
	let id = id_of_label l in 
	(match Extraction.constant_kind !cur_env cb with 
	   | Extraction.Logical -> () 
	   | Extraction.Type -> add upper_type (id_of_label l)
	   | Extraction.Term -> add false (id_of_label l))
    | (_, SEBmind mib) ->
	Array.iter 
	  (fun mip -> 
	     if mip.mind_sort = (Prop Null) then ()
	     else begin
	       add upper_type mip.mind_typename; 
	       Array.iter (add true) mip.mind_consnames
	     end)
	  mib.mind_packets
    | _ -> ()
  in
  match (Environ.lookup_module mp !cur_env).mod_expr with 
    | Some (MEBstruct (_,msb)) -> List.iter contents_seb msb; (mp,!s)
    | _ -> mp,!s

(* The previous functions might fail if [mp] isn't a directly visible module. *)
(* Ex: [MPself] under functor, [MPbound], etc ... *)
(* Exception [Not_found] is catched in [pp_global]. *) 

let contents_first_level = 
  let cache = ref MPmap.empty in 
  fun mp -> 
    try MPmap.find mp !cache 
    with Not_found -> 
      let res = contents_first_level mp in 
      cache := MPmap.add mp res !cache; 
      res

let modules_first_level mp = 
  let s = ref Stringset.empty in 
  let add id = s := Stringset.add (rename_module id) !s in 
  let contents_seb = function 
    | (l, (SEBmodule _ | SEBmodtype _)) -> add (id_of_label l) 
    | _ -> ()
  in
  match (Environ.lookup_module mp !cur_env).mod_expr with 
    | Some (MEBstruct (_,msb)) -> List.iter contents_seb msb; !s
    | _ -> !s

let rec clash_in_contents mp0 s = function  
  | [] -> false
  | (mp,_) :: _ when mp = mp0 -> false
  | (mp,ss) :: l -> (Stringset.mem s ss) || (clash_in_contents mp0 s l) 

let create_modular_renamings struc = 
  let cur_mp = fst (List.hd struc) in
  let modfiles = ref MPset.empty in 
  let { up = u ; down = d } = struct_get_references struc 
  in 
  (* 1) create renamings of objects *)
  let add upper r = 
    let mp = modpath (kn_of_r r) in 
    begin try 
      let mp = modfile_of_mp mp in 
      if mp <> cur_mp then modfiles := MPset.add mp !modfiles
    with Not_found -> () 
    end; 
    let mplist = mp_to_list (modpath (kn_of_r r)) in 
    let s = modular_rename upper (id_of_global r) in 
    global_ids := Idset.add (id_of_string s) !global_ids;    
    Hashtbl.add renamings r (mplist,s)
  in
  Refset.iter (add true) (Orefset.set u); 
  Refset.iter (add false) (Orefset.set d); 
  
  (* 2) determine the opened libraries and the potential clashes *)
  let used_modules = MPset.elements !modfiles in 
  let s = ref (modules_first_level cur_mp) in 
  List.iter 
    (function 
       | MPfile d -> 
	   let s_mp = 
	     String.capitalize (string_of_id (List.hd (repr_dirpath d))) in 
	   if Stringset.mem s_mp !s then error_module_clash s_mp 
	   else s:= Stringset.add s_mp !s 
       | _ -> assert false)
    used_modules;
  let env = List.rev_map contents_first_level used_modules in 
  let needs_qualify r = 
    let mp = modpath (kn_of_r r) in 
    if not (is_modfile mp) || mp = cur_mp then () 
    else
      let s = snd (get_renamings r) in 
      if clash_in_contents mp s env 
      then must_qualify := Refset.add r !must_qualify
  in 
  Refset.iter needs_qualify (Orefset.set u);
  Refset.iter needs_qualify (Orefset.set d); 
  used_modules

let create_mono_renamings struc = 
  let fst_level_modules = ref Idmap.empty in 
  let { up = u ; down = d } = struct_get_references struc 
  in 
  (* 1) create renamings of objects *)
  let add upper r = 
    let mp = modpath (kn_of_r r) in 
    begin try 
      let mp,l = fst_level_module_of_mp mp in
      let id = id_of_label l in 
      if Idmap.find id !fst_level_modules <> mp then 
	error_module_clash (string_of_id id) 
      else fst_level_modules := Idmap.add id mp !fst_level_modules
    with Not_found -> ()
    end;
    let mplist = mp_to_list' (modpath (kn_of_r r)) in 
    let my_id = if upper then uppercase_id else lowercase_id in
    let id = 
      if mplist = [] then 
	next_ident_away (my_id (id_of_global r)) (Idset.elements !global_ids)
      else id_of_string (modular_rename upper (id_of_global r)) 
    in 
    global_ids := Idset.add id !global_ids;    
    Hashtbl.add renamings r (mplist,string_of_id id)
  in
  List.iter (add true) (List.rev (Orefset.list u)); 
  List.iter (add false) (List.rev (Orefset.list d))
		    
(*s Renaming issues at toplevel *)

module ToplevelParams = struct
  let globals () = Idset.empty
  let pp_global _ r = pr_global r
  let pp_long_module _ mp = str (string_of_mp mp)
  let pp_short_module id = pr_id id
end

(*s Renaming issues for a monolithic or modular extraction. *)

let rec remove_common l l' = match l,l' with 
  | [], _ -> l' 
  | s::q, s'::q' -> if s = s' then remove_common q q' else l'
  | _ -> assert false 

let rec length_common_prefix l l' = match l,l' with 
  | [],_ -> 0
  | _, [] -> 0 
  | s::q, s'::q' -> if s <> s' then 0 else 1+(length_common_prefix q q')

let rec decreasing_contents mp = match mp with 
  | MPdot (mp',_) -> (contents_first_level mp) :: (decreasing_contents mp')
  | mp when is_toplevel mp -> [] 
  | _ -> [contents_first_level mp]

module StdParams = struct

  let globals () = !global_ids

  let pp_global cur_mp r = 
    let cur_mp = long_mp cur_mp in 
    let cur_l = if !modular then mp_to_list cur_mp else mp_to_list' cur_mp in 
    let r = long_r r in 
    let mp = modpath (kn_of_r r) in 
    let l,s = get_renamings r in 
    let n = length_common_prefix cur_l l in 
    if n = 0 && !modular (* [r] is in another module *)
    then 
      if (Refset.mem r !must_qualify) || (lang () = Haskell)
      then str (string_of_ren l s)
      else 
	try 
	  if clash_in_contents mp s (decreasing_contents cur_mp) 
	  then str (string_of_ren l s)
	  else str s
	with Not_found -> str (string_of_ren l s) 
    else 
      let nl = List.length l in 
      if n = nl && nl < List.length cur_l then (* strict prefix *)
	try 
	  if clash_in_contents mp s (decreasing_contents cur_mp) 
	  then error_unqualified_name (string_of_ren l s) (string_of_modlist cur_l)
	  else str s
	with Not_found -> str (string_of_ren l s)
      else (* [cur_mp] and [mp] are orthogonal *)
	let l = remove_common cur_l l 
	in str (string_of_ren l s)
	     
  let pp_long_module cur_mp mp = 
    let cur_mp = long_mp cur_mp in 
    let cur_l = if !modular then mp_to_list cur_mp else mp_to_list' cur_mp in 
    let mp = long_mp mp in 
    let l = if !modular then mp_to_list mp else mp_to_list' mp in 
    str (string_of_modlist (remove_common cur_l l))

  let pp_short_module id = str (rename_module id)
end

module ToplevelPp = Ocaml.Make(ToplevelParams)
module OcamlPp = Ocaml.Make(StdParams)
module HaskellPp = Haskell.Make(StdParams)
module SchemePp = Scheme.Make(StdParams)

let pp_decl mp d = match lang () with 
  | Ocaml -> OcamlPp.pp_decl mp d 
  | Haskell -> HaskellPp.pp_decl mp d
  | Scheme -> SchemePp.pp_decl mp d 
  | Toplevel -> ToplevelPp.pp_decl mp d 

let pp_struct s = match lang () with 
  | Ocaml -> OcamlPp.pp_struct s 
  | Haskell -> HaskellPp.pp_struct s
  | Scheme -> SchemePp.pp_struct s
  | Toplevel -> ToplevelPp.pp_struct s

let pp_signature s = match lang () with 
  | Ocaml -> OcamlPp.pp_signature s 
  | Haskell -> HaskellPp.pp_signature s
  | _ -> assert false

let set_keywords () =
  (match lang () with 
    | Ocaml -> keywords := Ocaml.keywords
    | Haskell -> keywords := Haskell.keywords
    | Scheme -> keywords := Scheme.keywords
    | Toplevel -> keywords := Idset.empty);
  global_ids := !keywords; 
  must_qualify := Refset.empty
    
let preamble prm = match lang () with 
  | Ocaml -> Ocaml.preamble prm   
  | Haskell -> Haskell.preamble prm
  | Scheme -> Scheme.preamble prm
  | Toplevel -> (fun _ _ -> mt ())

let preamble_sig prm = match lang () with 
  | Ocaml -> Ocaml.preamble_sig prm   
  | _ -> assert false

(*S Extraction of one decl to stdout. *)

let print_one_decl struc mp decl = 
  set_keywords (); 
  modular := false; 
  create_mono_renamings struc;
  msgnl (pp_decl mp decl)

(*S Extraction to a file. *)

let print_structure_to_file f prm struc =
  cons_cofix := Refset.empty;
  Hashtbl.clear renamings;
  set_keywords ();
  modular := prm.modular; 
  let used_modules =
    if lang () = Toplevel then [] 
    else if prm.modular then create_modular_renamings struc
    else (create_mono_renamings struc; [])
  in 
  let print_dummys =
    (struct_ast_search MLdummy struc, 
     struct_type_search Tdummy struc, 
     struct_type_search Tunknown struc)
  in
  (* print the implementation *)
  let cout = match f with None -> stdout | Some (f,_) -> open_out f in
  let ft = Pp_control.with_output_to cout in
  begin try 
    msg_with ft (preamble prm used_modules print_dummys);
    msg_with ft (pp_struct struc);
    if f <> None then close_out cout;
  with e -> 
    if f <> None then close_out cout; raise e 
  end;
  (* print the signature *)
  match f with 
    | Some (_,f) when lang () = Ocaml -> 
	let cout = open_out f in
	let ft = Pp_control.with_output_to cout in
	begin try 
	  msg_with ft (preamble_sig prm used_modules print_dummys);
	  msg_with ft (pp_signature (signature_of_structure struc));
	  close_out cout;
	with e -> 
	  close_out cout; raise e 
	end
    | _ -> () 

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







