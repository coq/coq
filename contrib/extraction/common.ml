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
open Modutil
open Ocaml

(*S Renamings. *)

(*s Tables of global renamings *)

let keywords = ref Idset.empty
let global_ids = ref Idset.empty
let modular = ref false

let renamings = Hashtbl.create 97
let rename r s = Hashtbl.add renamings r s
let get_renamings r = Hashtbl.find renamings r 

let modvisited = ref MPset.empty
let modcontents = ref Gset.empty
let add_module_contents mp s = modcontents := Gset.add (mp,s) !modcontents
let module_contents mp s = Gset.mem (mp,s) !modcontents

let to_qualify = ref Refset.empty

(*s Uppercase/lowercase renamings. *) 

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

let print_labels = List.map (fun l -> rename_module (id_of_label l))

let print_base_mp = function 
  | MPfile d -> String.capitalize (string_of_id (List.hd (repr_dirpath d)))
  | MPself msid -> rename_module (id_of_msid msid)
  | MPbound mbid -> rename_module (id_of_mbid mbid)
  | _ -> assert false

(*s From a [module_path] to a list of [identifier]. *)

let mp2l mp = 
  let base_mp,l = labels_of_mp mp in 
  if !modular || not (at_toplevel base_mp)
  then (print_base_mp base_mp) :: (print_labels l)
  else print_labels l 

let string_of_modlist l = 
  List.fold_right (fun s s' -> if s' = "" then s else s ^ "." ^ s') l ""

let string_of_ren l s = 
  if l = [] then s else (string_of_modlist l)^"."^s

(* [clash mp0 l s mpl] checks if [mp0-l-s] can be printed as [l-s] when 
   [mpl] is the context of visible modules. More precisely, we check if 
   there exists a mp1, module (sub-)path of an element of [mpl], such as 
   module [mp1-l] contains [s]. 
   The verification stops if we encounter [mp1=mp0]. *)

exception Stop 

let clash mp0 l s mpl = 
  let rec clash_one mp = match mp with
    | _ when mp = mp0 -> raise Stop
    | MPdot (mp',_) -> 
	(module_contents (add_labels_mp mp l) s) || (clash_one mp') 
    | mp when is_toplevel mp -> false
    | _ -> module_contents (add_labels_mp mp l) s
  in
  let rec clash_list = function 
    | [] -> false
    | mp :: mpl -> (clash_one mp) || (clash_list mpl) 
  in try clash_list mpl with Stop -> false

(*s [contents_first_level mp] finds the names of the first-level objects 
  exported by module [mp]. Nota: it might fail if [mp] isn't a directly 
  visible module. Ex: [MPself] under functor, [MPbound], etc ... *)

let contents_first_level mp = 
  if not (MPset.mem mp !modvisited) then begin 
    modvisited := MPset.add mp !modvisited; 
    match (Global.lookup_module mp).mod_type with 
      | MTBsig (msid,msb) -> 
	  let add b id = add_module_contents mp (modular_rename b id) in 
	  let upper_type = (lang () = Haskell) in
	  List.iter 
	    (function 
	       | (l, SPBconst cb) -> 
		   (match Extraction.constant_kind (Global.env ()) cb with 
		      | Extraction.Logical -> () 
		      | Extraction.Type -> add upper_type (id_of_label l)
		      | Extraction.Term -> add false (id_of_label l))
	       | (_, SPBmind mib) ->
		   Array.iter 
		     (fun mip -> if mip.mind_sort <> (Prop Null) then begin
			add upper_type mip.mind_typename; 
			Array.iter (add true) mip.mind_consnames
		      end)
		     mib.mind_packets
	       | _ -> ())
	    (Modops.subst_signature_msid msid mp msb)
      | _ -> ()
  end

(*s Initial renamings creation, for modular extraction. *) 

let create_modular_renamings struc = 
  let current_module = fst (List.hd struc) in 
  let modfiles = ref MPset.empty in 
  let { up = u ; down = d } = struct_get_references_set struc 
  in 
  (* 1) creates renamings of objects *)
  let add upper r = 
    let mp = modpath (kn_of_r r) in 
    begin try 
      let mp = modfile_of_mp mp in 
      if mp <> current_module then modfiles := MPset.add mp !modfiles
    with Not_found -> () 
    end; 
    let s = modular_rename upper (id_of_global r) in 
    global_ids := Idset.add (id_of_string s) !global_ids;    
    Hashtbl.add renamings r s
  in
  Refset.iter (add true) u; 
  Refset.iter (add false) d; 
  
  (* 2) determines the opened libraries. *)
  let used_modules = MPset.elements !modfiles in 

  (* [s] will contain all first-level sub-modules of [cur_mp] *)
  let s = ref Stringset.empty in 
  begin 
    let add l = s := Stringset.add (rename_module (id_of_label l)) !s in 
    match (Global.lookup_module current_module).mod_type with 
      | MTBsig (_,msb) ->
	  List.iter (function (l,SPBmodule _) -> add l | _ -> ()) msb
      | _ -> ()
  end;
  (* We now compare [s] with the modules coming from [used_modules]. *)
  List.iter 
    (function 
       | MPfile d -> 
	   let s_mp = 
	     String.capitalize (string_of_id (List.hd (repr_dirpath d))) in 
	   if Stringset.mem s_mp !s then error_module_clash s_mp 
	   else s:= Stringset.add s_mp !s 
       | _ -> assert false)
    used_modules;

  (* 3) determines the potential clashes *)
  List.iter contents_first_level used_modules; 
  let used_modules' = List.rev used_modules in 
  let needs_qualify r = 
    let mp = modpath (kn_of_r r) in 
    if (is_modfile mp) && mp <> current_module && 
      (clash mp [] (get_renamings r) used_modules')
    then to_qualify := Refset.add r !to_qualify
  in
  Refset.iter needs_qualify u;
  Refset.iter needs_qualify d; 
  used_modules

(*s Initial renamings creation, for monolithic extraction. *)

let create_mono_renamings struc = 
  let fst_level_modules = ref Idmap.empty in 
  let { up = u ; down = d } = struct_get_references_list struc 
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
    let my_id = if upper then uppercase_id else lowercase_id in
    let id = 
      if at_toplevel (modpath (kn_of_r r)) then 
	next_ident_away (my_id (id_of_global r)) (Idset.elements !global_ids)
      else id_of_string (modular_rename upper (id_of_global r)) 
    in 
    global_ids := Idset.add id !global_ids;    
    Hashtbl.add renamings r (string_of_id id) 
  in
  List.iter (add true) (List.rev u); 
  List.iter (add false) (List.rev d)
		    
(*s Renaming issues at toplevel *)

module TopParams = struct
  let globals () = Idset.empty
  let pp_global _ r = pr_id (id_of_global r)
  let pp_long_module _ mp = str (string_of_mp mp)
  let pp_short_module id = pr_id id
end

(*s Renaming issues for a monolithic or modular extraction. *)

module StdParams = struct

  let globals () = !global_ids

  (* TODO: remettre des conditions [lang () = Haskell] disant de qualifier. *)

  let pp_global mpl r = 
    let s = get_renamings r in 
    let mp = modpath (kn_of_r r) in 
    let final = 
      if mp = List.hd mpl then s (* simpliest situation *)
      else 
	try (* has [mp] something in common with one of those in [mpl] ? *)
	  let pref = common_prefix_from_list mp mpl in 
	  let l = labels_after_prefix pref mp in 
(*i TODO:  traiter proprement.
          if clash pref l s mpl 
	  then error_unqualified_name (string_of_ren (print_labels l) s) 
	    (string_of_modlist (mp2l (List.hd mpl)))
	  else i*) 
	  string_of_ren (print_labels l) s
	with Not_found -> (* [mp] is othogonal with every element of [mp]. *)
	  let base, l = labels_of_mp mp in 
	  let short = string_of_ren (print_labels l) s in
	  if not (at_toplevel mp) ||
	    (!modular && 
	     (l <> [] || (Refset.mem r !to_qualify) || (clash base l s mpl)))
	  then (print_base_mp base)^"."^short
	  else short
    in 
    add_module_contents mp s; (* update the visible environment *)
    str s

  let pp_long_module mpl mp = 
    try (* has [mp] something in common with one of those in [mpl] ? *)
      let pref = common_prefix_from_list mp mpl in 
      let l = labels_after_prefix pref mp in 
(*i   TODO: comment adapter cela ??   
      if clash pref l s mpl 
      then error_unqualified_name (string_of_ren (print_labels l) s) 
	(string_of_modlist (mp2l (List.hd mpl))) 
      else 
i*)	
      str (string_of_modlist (print_labels l))
    with Not_found -> (* [mp] is othogonal with every element of [mp]. *)
      let base_mp, l = labels_of_mp mp in 
      let short = string_of_modlist (print_labels l) in
      if not (at_toplevel mp) || !modular 
      then str ((print_base_mp base_mp)^(if short = "" then "" else "."^short))
      else str short

  let pp_short_module id = str (rename_module id)
end

module ToplevelPp = Ocaml.Make(TopParams)
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
  to_qualify := Refset.empty
    
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
  msgnl (pp_decl [mp] decl)

(*S Extraction to a file. *)

let print_structure_to_file f prm struc =
  cons_cofix := Refset.empty;
  Hashtbl.clear renamings;
  modcontents := Gset.empty;
  modvisited := MPset.empty; 
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
  let cout = option_app (fun (f,_) -> open_out f) f in 
  let ft = match cout with 
    | None -> !Pp_control.std_ft
    | Some cout -> Pp_control.with_output_to cout in 
  begin try 
    msg_with ft (preamble prm used_modules print_dummys);
    msg_with ft (pp_struct struc);
    option_iter close_out cout; 
  with e -> 
    option_iter close_out cout; raise e
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







