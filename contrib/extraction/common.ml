(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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

(* For each [global_reference], this table will contain the different parts 
   of its renamings, in [string list] form. *)
let renamings = Hashtbl.create 97
let rename r l = Hashtbl.add renamings r l
let get_renamings r = Hashtbl.find renamings r 

(* Idem for [module_path]. *)
let mp_renamings = Hashtbl.create 97
let mp_rename mp l = Hashtbl.add mp_renamings mp l
let mp_get_renamings mp = Hashtbl.find mp_renamings mp 

let modvisited = ref MPset.empty
let modcontents = ref Gset.empty
let add_module_contents mp s = modcontents := Gset.add (mp,s) !modcontents
let module_contents mp s = Gset.mem (mp,s) !modcontents

let to_qualify = ref Refset.empty

let mod_1st_level = ref Idmap.empty

(*s Uppercase/lowercase renamings. *) 

let is_upper s = match s.[0] with 'A' .. 'Z' -> true | _ -> false

let is_lower s = match s.[0] with 'a' .. 'z' | '_' -> true | _ -> false

(* This function creates from [id] a correct uppercase/lowercase identifier. 
   This is done by adding a [Coq_] or [coq_] prefix. To avoid potential clashes 
   with previous [Coq_id] variable, these prefixes are duplicated if already 
   existing. *)

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

let rec mp_create_modular_renamings mp = 
  try mp_get_renamings mp 
  with Not_found -> 
    let ren = match mp with 
      | MPdot (mp,l) -> 
	  (rename_module (id_of_label l)) :: (mp_create_modular_renamings mp)
      | MPself msid -> [rename_module (id_of_msid msid)]
      | MPbound mbid -> [rename_module (id_of_mbid mbid)]
      | MPfile f -> [String.capitalize (string_of_id (List.hd (repr_dirpath f)))]
    in mp_rename mp ren; ren


let create_modular_renamings struc = 
  let current_module = fst (List.hd struc) in 
  let modfiles = ref MPset.empty in 
  let { up = u ; down = d } = struct_get_references_set struc 
  in 
  (* 1) creates renamings of objects *)
  let add upper r = 
    let mp = modpath (kn_of_r r) in 
    let l = mp_create_modular_renamings mp in 
    let s = modular_rename upper (id_of_global r) in 
    global_ids := Idset.add (id_of_string s) !global_ids;    
    rename r (s::l); 
    begin try 
      let mp = modfile_of_mp mp in 
      if mp <> current_module then modfiles := MPset.add mp !modfiles
    with Not_found -> () 
    end; 
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
      (clash mp [] (List.hd (get_renamings r)) used_modules')
    then to_qualify := Refset.add r !to_qualify
  in
  Refset.iter needs_qualify u;
  Refset.iter needs_qualify d; 
  used_modules

(*s Initial renamings creation, for monolithic extraction. *)

let begins_with_CoqXX s = 
  (String.length s >= 4) && 
  (String.sub s 0 3 = "Coq") &&
  (try 
     for i = 4 to (String.index s '_')-1 do 
       match s.[i] with 
	 | '0'..'9' -> () 
	 | _ -> raise Not_found
     done; 
     true
   with Not_found -> false)

let mod_1st_level_rename l =
  let coqid = id_of_string "Coq" in 
  let id = id_of_label l in 
  try 
    let coqset = Idmap.find id !mod_1st_level in 
    let nextcoq = next_ident_away coqid coqset in 
    mod_1st_level := Idmap.add id (nextcoq::coqset) !mod_1st_level; 
    (string_of_id nextcoq)^"_"^(string_of_id id) 
  with Not_found -> 
    let s = string_of_id id in 
    if is_lower s || begins_with_CoqXX s then
      (mod_1st_level := Idmap.add id [coqid] !mod_1st_level; "Coq_"^s)
    else
      (mod_1st_level := Idmap.add id [] !mod_1st_level; s)

let rec mp_create_mono_renamings mp = 
  try mp_get_renamings mp 
  with Not_found -> 
    let ren = match mp with 
       | _ when (at_toplevel mp) -> [""]
       | MPdot (mp,l) -> 
	   let lmp = mp_create_mono_renamings mp in
	   if lmp = [""] then (mod_1st_level_rename l)::lmp
	   else (rename_module (id_of_label l))::lmp
       | MPself msid -> [rename_module (id_of_msid msid)]
       | MPbound mbid -> [rename_module (id_of_mbid mbid)]
       | _ -> assert false
    in mp_rename mp ren; ren

let create_mono_renamings struc = 
  let { up = u ; down = d } = struct_get_references_list struc in 
  let add upper r = 
    let mp = modpath (kn_of_r r) in 
    let l = mp_create_mono_renamings mp in
    let mycase = if upper then uppercase_id else lowercase_id in 
    let id = 
      if l = [""] then 
	next_ident_away (mycase (id_of_global r)) (Idset.elements !global_ids)
      else id_of_string (modular_rename upper (id_of_global r))
    in 
    global_ids := Idset.add id !global_ids;    
    rename r ((string_of_id id)::l) 
  in
  List.iter (add true) (List.rev u); 
  List.iter (add false) (List.rev d)
		    
(*s Renaming issues at toplevel *)

module TopParams = struct
  let globals () = Idset.empty
  let pp_global _ r = pr_id (id_of_global r)
  let pp_module _ mp = str (string_of_mp mp)
end

(*s Renaming issues for a monolithic or modular extraction. *)

module StdParams = struct

  let globals () = !global_ids

  (* TODO: remettre des conditions [lang () = Haskell] disant de qualifier. *)

  let rec dottify = function 
    | [] -> assert false 
    | [s] -> s 
    | s::[""] -> s 
    | s::l -> (dottify l)^"."^s

  let pp_global mpl r = 
    let ls = get_renamings r in 
    let s = List.hd ls in 
    let mp = modpath (kn_of_r r) in 
    let ls = 
      if mp = List.hd mpl then [s] (* simpliest situation *)
      else 
	try (* has [mp] something in common with one of those in [mpl] ? *)
	  let pref = common_prefix_from_list mp mpl in 
	  (*i TODO: possibilité de clash i*)
	  list_firstn ((mp_length mp)-(mp_length pref)+1) ls
	with Not_found -> (* [mp] is othogonal with every element of [mp]. *)
	  let base = base_mp mp in 
	  if !modular &&  
	    (at_toplevel mp) && 
	    not (Refset.mem r !to_qualify) && 
	    not (clash base [] s mpl) 
	  then snd (list_sep_last ls)
	  else ls
    in 
    add_module_contents mp s; (* update the visible environment *)
    str (dottify ls)

  let pp_module mpl mp = 
    let ls = 
      if !modular 
      then mp_create_modular_renamings mp 
      else mp_create_mono_renamings mp 
    in 
    let ls = 
      try (* has [mp] something in common with one of those in [mpl] ? *)
	let pref = common_prefix_from_list mp mpl in 
	(*i TODO: clash possible i*)
	list_firstn ((mp_length mp)-(mp_length pref)) ls
      with Not_found -> (* [mp] is othogonal with every element of [mp]. *)
	let base = base_mp mp in 
	if !modular && (at_toplevel mp) 
	then snd (list_sep_last ls)
	else ls
    in str (dottify ls) 

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
  | Toplevel -> (fun _ _ _ -> mt ())

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

let info f = 
  Options.if_verbose msgnl 
    (str ("The file "^f^" has been created by extraction."))

let print_structure_to_file f prm struc =
  Hashtbl.clear renamings;
  mod_1st_level := Idmap.empty; 
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
    (struct_ast_search ((=) MLdummy) struc, 
     struct_type_search Tdummy struc, 
     struct_type_search Tunknown struc)
  in 
  let print_magic = 
    if lang () <> Haskell then false 
    else struct_ast_search (function MLmagic _ -> true | _ -> false) struc
  in
  (* print the implementation *)
  let cout = option_app (fun (f,_) -> open_out f) f in 
  let ft = match cout with 
    | None -> !Pp_control.std_ft
    | Some cout -> Pp_control.with_output_to cout in 
  begin try 
    msg_with ft (preamble prm used_modules print_dummys print_magic);
    msg_with ft (pp_struct struc);
    option_iter close_out cout; 
  with e -> 
    option_iter close_out cout; raise e
  end;
  option_iter (fun (f,_) -> info f) f;
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
	end; 
	info f 
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







