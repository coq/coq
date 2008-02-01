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
open Mlutil
open Modutil
open Mod_subst

(*s Some pretty-print utility functions. *)

let pp_par par st = if par then str "(" ++ st ++ str ")" else st

let pp_apply st par args = match args with
  | [] -> st
  | _  -> hov 2 (pp_par par (st ++ spc () ++ prlist_with_sep spc identity args))

let pr_binding = function
  | [] -> mt ()
  | l  -> str " " ++ prlist_with_sep (fun () -> str " ") pr_id l

let fnl2 () = fnl () ++ fnl () 

let space_if = function true -> str " " | false -> mt ()

let sec_space_if = function true -> spc () | false -> mt ()

let is_digit = function 
  | '0'..'9' -> true
  | _ -> false

let begins_with_CoqXX s = 
  let n = String.length s in 
  n >= 4 && s.[0] = 'C' && s.[1] = 'o' && s.[2] = 'q' &&
  let i = ref 3 in 
  try while !i < n do
    if s.[!i] = '_' then i:=n (*Stop*)
    else if is_digit s.[!i] then incr i 
    else raise Not_found
  done; true
  with Not_found -> false
  
let unquote s = 
  if lang () <> Scheme then s 
  else 
    let s = String.copy s in 
    for i=0 to String.length s - 1 do if s.[i] = '\'' then s.[i] <- '~' done;
    s
      
let rec dottify = function 
  | [] -> assert false 
  | [s] -> unquote s 
  | s::[""] -> unquote s 
  | s::l -> (dottify l)^"."^(unquote s)

(*s Uppercase/lowercase renamings. *) 

let is_upper s = match s.[0] with 'A' .. 'Z' -> true | _ -> false
let is_lower s = match s.[0] with 'a' .. 'z' | '_' -> true | _ -> false

let lowercase_id id = id_of_string (String.uncapitalize (string_of_id id))
let uppercase_id id = id_of_string (String.capitalize (string_of_id id))

(* [pr_upper_id id] makes 2 String.copy lesser than [pr_id (uppercase_id id)] *)
let pr_upper_id id = str (String.capitalize (string_of_id id))


(*s de Bruijn environments for programs *)

type env = identifier list * Idset.t

(*s Generic renaming issues for local variable names. *)

let rec rename_id id avoid = 
  if Idset.mem id avoid then rename_id (lift_ident id) avoid else id

let rec rename_vars avoid = function
  | [] -> 
      [], avoid
  | id :: idl when id == dummy_name ->
      (* we don't rename dummy binders *)
      let (idl', avoid') = rename_vars avoid idl in
      (id :: idl', avoid')
  | id :: idl ->
      let (idl, avoid) = rename_vars avoid idl in
      let id = rename_id (lowercase_id id) avoid in
      (id :: idl, Idset.add id avoid)

let rename_tvars avoid l = 
  let rec rename avoid = function 
    | [] -> [],avoid 
    | id :: idl -> 
	let id = rename_id (lowercase_id id) avoid in 
	let idl, avoid = rename (Idset.add id avoid) idl in 
	(id :: idl, avoid) in
  fst (rename avoid l)

let push_vars ids (db,avoid) =
  let ids',avoid' = rename_vars avoid ids in
  ids', (ids' @ db, avoid')

let get_db_name n (db,_) = 
  let id = List.nth db (pred n) in 
  if id = dummy_name then id_of_string "__" else id


(*S Renamings of global objects. *)

(*s Tables of global renamings *)

let keywords = ref Idset.empty
let set_keywords kws = keywords := kws

let global_ids = ref Idset.empty
let add_global_ids s = global_ids := Idset.add s !global_ids
let global_ids_list () = Idset.elements !global_ids

let empty_env () = [], !global_ids

let mktable () = 
  let h = Hashtbl.create 97 in 
  (Hashtbl.add h, Hashtbl.find h, fun () -> Hashtbl.clear h)

let mkset () = 
  let h = Hashtbl.create 97 in 
  (fun x -> Hashtbl.add h x ()), (Hashtbl.mem h), (fun () -> Hashtbl.clear h)

let mktriset () = 
  let h = Hashtbl.create 97 in
  (fun x y z -> Hashtbl.add h (x,y,z) ()), 
  (fun x y z -> Hashtbl.mem h (x,y,z)), 
  (fun () -> Hashtbl.clear h)

(* For each [global_reference], this table will contain the different parts 
   of its renaming, in [string list] form. *)
let add_renaming, get_renaming, clear_renaming = mktable ()

(* Idem for [module_path]. *)
let add_mp_renaming, get_mp_renaming, clear_mp_renaming = mktable ()

(* A table for function modfstlev_rename *)
let add_modfstlev, get_modfstlev, clear_modfstlev = mktable ()

(* A set of all external objects that will have to be fully qualified *)
let add_static_clash, static_clash, clear_static_clash = mkset ()

(* Two tables of triplets [kind * module_path * string]. The first one 
   will record the first level of all MPfile, not only the current one. 
   The second table will contains local renamings. *)

type kind = Term | Type | Cons | Mod

let add_ext_mpmem, ext_mpmem, clear_ext_mpmem = mktriset ()
let add_loc_mpmem, loc_mpmem, clear_loc_mpmem = mktriset ()

(* The list of external modules that will be opened initially *)
let add_mpfiles, mem_mpfiles, list_mpfiles, clear_mpfiles = 
  let m = ref MPset.empty in 
  (fun mp -> m:= MPset.add mp !m), 
  (fun mp -> MPset.mem mp !m),
  (fun () -> MPset.elements !m),
  (fun () -> m:= MPset.empty)

(*s table containing the visible horizon at a precise moment *)

let visible = ref ([] : module_path list)
let pop_visible () = visible := List.tl !visible
let push_visible mp = visible := mp :: !visible
let top_visible_mp () = List.hd !visible

(*s substitutions for printing signatures *)

let substs = ref empty_subst
let add_subst msid mp = substs := add_msid msid mp !substs
let subst_mp mp = subst_mp !substs mp
let subst_kn kn = subst_kn !substs kn
let subst_con c = fst (subst_con !substs c)
let subst_ref = function 
  | ConstRef con -> ConstRef (subst_con con)
  | IndRef (kn,i) -> IndRef (subst_kn kn,i)
  | ConstructRef ((kn,i),j) -> ConstructRef ((subst_kn kn,i),j)
  | _ -> assert false


let duplicate_index = ref 0
let to_duplicate = ref Gmap.empty
let add_duplicate mp l = 
  incr duplicate_index; 
  let ren = "Coq__" ^ string_of_int (!duplicate_index) in 
  to_duplicate := Gmap.add (mp,l) ren !to_duplicate
let check_duplicate mp l = 
  let mp' = subst_mp mp in 
  Gmap.find (mp',l) !to_duplicate

type reset_kind = OnlyLocal | AllButExternal | Everything

let reset_allbutext () = 
  clear_loc_mpmem (); 
  global_ids := !keywords; 
  clear_renaming (); 
  clear_mp_renaming (); 
  clear_modfstlev (); 
  clear_static_clash (); 
  clear_mpfiles (); 
  duplicate_index := 0; 
  to_duplicate := Gmap.empty; 
  visible := []; 
  substs := empty_subst
 
let reset_everything () = reset_allbutext (); clear_ext_mpmem ()

let reset_renaming_tables = function 
  | OnlyLocal -> clear_loc_mpmem ()
  | AllButExternal -> reset_allbutext ()
  | Everything -> reset_everything ()

(*S Renaming functions *)

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

(*s [record_contents_fstlev] finds the names of the first-level objects 
  exported by the ground-level modules in [struc]. *)

let rec record_contents_fstlev struc = 
  let upper_type = (lang () = Haskell) in 
  let addtyp mp id = add_ext_mpmem Type mp (modular_rename upper_type id) in
  let addcons mp id = add_ext_mpmem Cons mp (modular_rename true id) in
  let addterm mp id = add_ext_mpmem Term mp (modular_rename false id) in
  let addmod mp id = add_ext_mpmem Mod mp (modular_rename true id) in 
  let addfix mp r = 
    add_ext_mpmem Term mp (modular_rename false (id_of_global r))
  in
  let f mp = function 
    | (l,SEdecl (Dind (_,ind))) -> 
	Array.iter 
	  (fun ip -> 
	     addtyp mp ip.ip_typename; Array.iter (addcons mp) ip.ip_consnames)
	  ind.ind_packets
    | (l,SEdecl (Dtype _)) -> addtyp mp (id_of_label l)
    | (l,SEdecl (Dterm _)) -> addterm mp (id_of_label l)
    | (l,SEdecl (Dfix  (rv,_,_))) -> Array.iter (addfix mp) rv
    | (l,SEmodule _) -> addmod mp (id_of_label l)
    | (l,SEmodtype _) -> addmod mp (id_of_label l)
  in
  List.iter (fun (mp,sel) -> List.iter (f mp) sel) struc

(*s For monolithic extraction, first-level modules might have to be renamed 
    with unique numbers *)

let modfstlev_rename l =
  let coqid = id_of_string "Coq" in 
  let id = id_of_label l in 
  try 
    let coqset = get_modfstlev id in 
    let nextcoq = next_ident_away coqid coqset in 
    add_modfstlev id (nextcoq::coqset); 
    (string_of_id nextcoq)^"_"^(string_of_id id) 
  with Not_found -> 
    let s = string_of_id id in 
    if is_lower s || begins_with_CoqXX s then
      (add_modfstlev id [coqid]; "Coq_"^s)
    else
      (add_modfstlev id []; s)


(*s Creating renaming for a [module_path] *)

let rec mp_create_renaming mp = 
  try get_mp_renaming mp 
  with Not_found -> 
    let ren = match mp with 
      | _ when not (modular ()) && at_toplevel mp -> [""]
      | MPdot (mp,l) -> 
	  let lmp = mp_create_renaming mp in 
	  if lmp = [""] then (modfstlev_rename l)::lmp
	  else (modular_rename true (id_of_label l))::lmp
      | MPself msid -> [modular_rename true (id_of_msid msid)]
      | MPbound mbid -> [modular_rename true (id_of_mbid mbid)]
      | MPfile _ when not (modular ()) -> assert false
      | MPfile _ -> [string_of_modfile mp]
    in add_mp_renaming mp ren; ren

(* [clash mp0 s mpl] checks if [mp0-s] can be printed as [s] when 
   [mpl] is the context of visible modules. More precisely, we check if 
   there exists a [mp] in [mpl] that contains [s]. 
   The verification stops if we encounter [mp=mp0]. *)

let rec clash mem mp0 s = function 
  | [] -> false
  | mp :: _ when mp = mp0 -> false
  | mp :: mpl -> mem mp s || clash mem mp0 s mpl
    
(*s Initial renamings creation, for modular extraction. *) 

let create_modular_renamings struc = 
  let current_module = fst (List.hd struc) in 
  let { typ = ty ; trm = tr ; cons = co } = struct_get_references_set struc 
  in 
  (* 1) creates renamings of objects *)
  let add upper r = 
    let mp = modpath_of_r r in 
    let l = mp_create_renaming mp in 
    let s = modular_rename upper (id_of_global r) in 
    add_global_ids (id_of_string s);
    add_renaming r (s::l); 
    begin try 
      let mp = modfile_of_mp mp in if mp <> current_module then add_mpfiles mp
    with Not_found -> () 
    end; 
  in
  Refset.iter (add (lang () = Haskell)) ty; 
  Refset.iter (add true) co;
  Refset.iter (add false) tr;
  
  (* 2) determines the opened libraries. *)
  let used_modules = list_mpfiles () in 
  let used_modules' = List.rev used_modules in 
  let str_list = List.map string_of_modfile used_modules' 
  in
  let rec check_elsewhere mpl sl = match mpl, sl with
    | [], [] -> []
    | mp::mpl, _::sl -> 
	if List.exists (ext_mpmem Mod mp) sl then
	  check_elsewhere mpl sl
	else mp :: (check_elsewhere mpl sl)
    | _ -> assert false
  in 
  let opened_modules = check_elsewhere used_modules' str_list in 
  clear_mpfiles (); 
  List.iter add_mpfiles opened_modules; 

  (* 3) determines the potential clashes *)
  let needs_qualify k r = 
    let mp = modpath_of_r r in 
      if (is_modfile mp) && mp <> current_module && 
	(clash (ext_mpmem k) mp (List.hd (get_renaming r)) opened_modules)
      then add_static_clash r
  in
    Refset.iter (needs_qualify Type) ty;
    Refset.iter (needs_qualify Term) tr;
    Refset.iter (needs_qualify Cons) co;
    List.rev opened_modules

(*s Initial renamings creation, for monolithic extraction. *)

let create_mono_renamings struc = 
  let { typ = ty ; trm = tr ; cons = co } = struct_get_references_list struc in
  let add upper r = 
    let mp = modpath_of_r r in 
    let l = mp_create_renaming mp in
    let mycase = if upper then uppercase_id else lowercase_id in 
    let id = 
      if l = [""] then 
	next_ident_away (mycase (id_of_global r)) (global_ids_list ())
      else id_of_string (modular_rename upper (id_of_global r))
    in 
    add_global_ids id; 
    add_renaming r ((string_of_id id)::l) 
  in
  List.iter (add (lang () = Haskell)) (List.rev ty); 
  List.iter (add false) (List.rev tr);
  List.iter (add true) (List.rev co);
  []

let create_renamings struc = 
  if modular () then create_modular_renamings struc
  else create_mono_renamings struc
    
		    
(*s On-the-fly qualification issues for both monolithic or modular extraction. *)

let pp_global k r = 
  let ls = get_renaming r in 
  assert (List.length ls > 1); 
  let s = List.hd ls in 
  let mp = modpath_of_r r in 
  if mp = top_visible_mp () then 
    (* simpliest situation: definition of r (or use in the same context) *)
    (* we update the visible environment *)
    (add_loc_mpmem k mp s; unquote s)
  else match lang () with 
    | Scheme -> unquote s (* no modular Scheme extraction... *)
    | Haskell -> 
	(* for the moment we always qualify in modular Haskell *)
	if modular () then dottify ls else s
    | Ocaml -> 
	try (* has [mp] something in common with one of [!visible] ? *)
	  let prefix = common_prefix_from_list mp !visible in 
	  let delta = mp_length mp - mp_length prefix in 
	  let ls = list_firstn (delta+1) ls in 
	  (* Difficulty: in ocaml we cannot qualify more than [ls], 
             but this (not-so-long) name can in fact be hidden. Solution: 
	     duplication of the _definition_ of r in a Coq__XXX module *)
	  let s,ls' = list_sep_last ls in 
	  let k' = if ls' = [] then k else Mod in 
	  if clash (loc_mpmem k') prefix s !visible then 
	    let front = if ls' = [] then [s] else ls' in 
	    let l = get_nth_label delta r in 
	    try dottify (front @ [check_duplicate prefix l])
	    with Not_found -> add_duplicate prefix l; dottify ls
	  else dottify ls 
	with Not_found -> 
	  (* [mp] belongs to a closed module, not one of [!visible]. *)
	  let base = base_mp mp in 
	  let base_s,ls1 = list_sep_last ls in 
	  let s,ls2 = list_sep_last ls1 in  
	  let k' = if ls2 = [] then k else Mod in 
	  if modular () && (mem_mpfiles base) && 
	    not (static_clash r) && 
	    (* k' = Mod can't clash in an opened module, see earlier check *)
	    not (clash (loc_mpmem k') base s !visible)
	  then (* Standard situation of an object in another file: *)
	    (* Thanks to the "open" of this file we remove its name *) 
	    dottify ls1
	  else if clash (loc_mpmem Mod) base base_s !visible then 
	    error_module_clash base_s
	  else dottify ls 
	    
(* The next function is used only in Ocaml extraction...*)
let pp_module mp = 
  let ls = mp_create_renaming mp in
  if List.length ls = 1 then dottify ls 
  else match mp with 
    | MPdot (mp0,_) when mp0 = top_visible_mp () -> 
	(* simpliest situation: definition of mp (or use in the same context) *)
	(* we update the visible environment *)
	let s = List.hd ls in 
	add_loc_mpmem Mod mp0 s; s
    | _ ->
	try (* has [mp] something in common with one of those in [!visible] ? *)
	  let prefix = common_prefix_from_list mp !visible in 
	  assert (mp <> prefix); (* no use of mp as whole module from itself *)
	  let delta = mp_length mp - mp_length prefix in 
	  let ls = list_firstn delta ls in
	  (* Difficulty: in ocaml we cannot qualify more than [ls], 
	     but this (not-so-long) name can in fact be hidden. Solution: 
	     duplication of the _definition_ of mp via a Coq__XXX module *)
	  let s,ls' = list_sep_last ls in 
	  if clash (loc_mpmem Mod) prefix s !visible then 
	    let l = get_nth_label_mp delta mp in 
	    try dottify (ls' @ [check_duplicate prefix l])
	    with Not_found -> add_duplicate prefix l; dottify ls
	  else dottify ls
	with Not_found -> 
	  (* [mp] belongs to a closed module, not one of [!visible]. *)
	  let base = base_mp mp in 
	  let base_s,ls' = list_sep_last ls in 
	  let s = fst (list_sep_last ls) in 
	  if modular () && (mem_mpfiles base) &&
	    not (clash (loc_mpmem Mod) base s !visible)
	  then dottify ls'
	  else if clash (loc_mpmem Mod) base base_s !visible then 
	    error_module_clash base_s
	  else dottify ls


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
