(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Term
open Declarations
open Names
open Libnames
open Pp
open Util
open Miniml
open Table
open Extraction
open Mlutil
open Common

(*s Recursive computation of the global references to extract. 
    We use a set of functions visiting the extracted objects in
    a depth-first way.
    We maintain an (imperative) structure [visit'] containing
    the set of already visited references and the list of 
    references to extract. The entry point is the function [visit]:
    it first normalizes the reference, and then check it has already been 
    visisted; if not, it adds it to the set of visited references, then
    recursively traverses its extraction and finally adds it to the [result]. *)

(*  Recursive extracted environment for a list of reference: we just
    iterate [visit] on the list, starting with an empty
    extracted environment, and we return the reversed list of 
    declaration in the field [result]. *)

type visit' = { mutable visited : KNset.t; mutable result : ml_decl list }

let extract_env rl =
  let knset =  
    Refset.fold (compose KNset.add kn_of_r) (all_customs ()) KNset.empty in 
  let v = { visited = knset; result = [] } in 
  let rec visit r = 
    let kn = kn_of_r r in 
    if not (KNset.mem kn v.visited) then begin
      (* we put [kn] in [visited] first to avoid loops in inductive defs *)
      v.visited <- KNset.add kn v.visited;
      let d = extract_declaration !cur_env r in 
      decl_iter_references visit visit visit d;
      v.result <- d :: v.result
    end
  in 
  List.iter visit rl;
  List.rev v.result


(*s Obtaining Coq environment. *)

let toplevel_env () = 
  let seg = Lib.contents_after None in 
  let get_reference = function 
    | (_,kn), Lib.Leaf o ->
	let mp,_,l = repr_kn kn in 
	let seb = match Libobject.object_tag o with
	  | "CONSTANT" -> SEBconst (Global.lookup_constant kn)
	  | "INDUCTIVE" -> SEBmind (Global.lookup_mind kn) 
	  | "MODULE" -> SEBmodule (Global.lookup_module (MPdot (mp,l)))
	  | "MODULE TYPE" -> SEBmodtype (Global.lookup_modtype kn)
	  | _ -> failwith "caught"
	in l,seb
    | _ -> failwith "caught"
  in 
  match current_toplevel () with 
    | MPself msid -> MEBstruct (msid, List.rev (map_succeed get_reference seg))
    | _ -> assert false

let environment_until dir_opt = 
  let rec parse = function 
    | [] when dir_opt = None -> [current_toplevel (), toplevel_env ()]
    | [] -> [] 
    | d :: l -> 
	match (Global.lookup_module (MPfile d)).mod_expr with 
	  | Some meb -> 
	      if dir_opt = Some d then [MPfile d, meb]
	      else (MPfile d, meb) :: (parse l)
	  | _ -> assert false
  in parse (Library.loaded_libraries ())

(*s Aux. functions *)

let r_of_kn env kn = 
  try let _ = Environ.lookup_constant kn env in ConstRef kn
  with Not_found -> 
    try let _ = Environ.lookup_mind kn env in IndRef (kn,0) 
    with Not_found -> assert false

(* Add _all_ direct subobjects of a module, not only those exported. 
   Build on the Modops.add_signature model. *)

let add_structure mp msb env = 
  let add_one env (l,elem) = 
    let kn = make_kn mp empty_dirpath l in 
    match elem with 
      | SEBconst cb -> Environ.add_constant kn cb env 
      | SEBmind mib -> Environ.add_mind kn mib env 
      | SEBmodule mb -> Modops.add_module (MPdot (mp,l)) mb env 
      | SEBmodtype mtb -> Environ.add_modtype kn mtb env  
  in List.fold_left add_one env msb

let add_functor mbid mtb env = 
  Modops.add_module (MPbound mbid) (Modops.module_body_of_type mtb) env 

(*s First, we parse everything in order to produce 1) an env containing 
   every internal objects and 2) a table of aliases between short and long 
   [module_path]. *)

let rec init_env_seb loc abs = function 
  | l, SEBmodule mb -> 
      init_env_module loc (option_app (fun mp -> MPdot (mp,l)) abs) mb 
  | l, SEBmodtype mtb -> init_env_modtype loc mtb 
  | _ -> () 

and init_env_module loc abs mb = 
  option_iter (init_env_meb loc abs) mb.mod_expr

and init_env_meb loc abs = function 
  | MEBident mp -> ()
  | MEBapply (meb, meb',_) -> 
      init_env_meb loc None meb; init_env_meb loc None meb'
  | MEBfunctor (mbid, mtb, meb) -> 
      cur_env := add_functor mbid mtb !cur_env; 
      init_env_modtype loc mtb; 
      init_env_meb loc None meb 
  | MEBstruct (msid, msb) -> 
      let loc = MPself msid in 
      cur_env := add_structure loc msb !cur_env;
      option_iter (add_aliases loc) abs; 
      List.iter (init_env_seb loc abs) msb

and init_env_modtype loc = function 
  | MTBident mp -> ()
  | MTBfunsig (mbid, mtb, mtb') -> 
      cur_env := add_functor mbid mtb !cur_env; 
      init_env_modtype loc mtb; 
      init_env_modtype loc mtb'
  | MTBsig (msid, sign) -> 
      let loc = MPself msid in
      cur_env := Modops.add_signature loc sign !cur_env;
      List.iter (init_env_spec loc) sign
	
and init_env_spec loc = function 
  | l, SPBmodule {msb_modtype=mtb} -> init_env_modtype loc mtb 
  | l, SPBmodtype mtb -> init_env_modtype loc mtb
  | _ -> ()

let init_env l =
  cur_env := Global.env (); 
  List.iter 
    (fun (mp,meb) -> init_env_meb (current_toplevel ()) (Some mp) meb) l

(*s The extraction pass. *)

type visit = { mutable kn : KNset.t; mutable mp : MPset.t }

let in_kn v kn = KNset.mem (long_kn kn) v.kn
let in_mp v mp = MPset.mem (long_mp mp) v.mp

let visit_ref v r = 
  let kn = long_kn (kn_of_r r) in 
  v.kn <- KNset.add kn v.kn; 
  v.mp <- MPset.union (prefixes_mp (modpath kn)) v.mp

exception Impossible

let check_arity cb = 
  if Reduction.is_arity !cur_env cb.const_type then raise Impossible

let check_fix cb i = 
  match cb.const_body with 
    | None -> raise Impossible
    | Some lbody -> 
	match kind_of_term (Declarations.force lbody) with 
	  | Fix ((_,j),recd) when i=j -> check_arity cb; (true,recd)
	  | CoFix (j,recd) when i=j -> check_arity cb; (false,recd)
	  | _ -> raise Impossible

let factor_fix l cb msb = 
  let _,recd as check = check_fix cb 0 in 
  let n = Array.length (let fi,_,_ = recd in fi) in
  if n = 1 then [|l|], recd, msb
  else begin 
    if List.length msb < n-1 then raise Impossible; 
    let msb', msb'' = list_chop (n-1) msb in 
    let labels = Array.make n l in 
    list_iter_i 
      (fun j -> 
	 function 
	   | (l,SEBconst cb') -> 
	       if check <> check_fix cb' (j+1) then raise Impossible; 
	       labels.(j+1) <- l; 
	   | _ -> raise Impossible) msb'; 
    labels, recd, msb''
  end

let logical_decl = function 
  | Dterm (_,MLdummy,Tdummy) -> true
  | Dtype (_,[],Tdummy) -> true 
  | Dfix (_,av,tv) -> 
      (array_for_all ((=) MLdummy) av) && (array_for_all ((=) Tdummy) tv)
  | Dind (_,i) -> array_for_all (fun ip -> ip.ip_logical) i.ind_packets
  | _ -> false

let logical_spec = function 
  | Stype (_, [], Some Tdummy) -> true
  | Sval (_,Tdummy) -> true
  | Sind (_,i) -> array_for_all (fun ip -> ip.ip_logical) i.ind_packets
  | _ -> false

let get_decl_references v d = 
  let f = visit_ref v in decl_iter_references f f f d

let get_spec_references v s = 
  let f = visit_ref v in spec_iter_references f f f s

let rec extract_msb v all loc = function 
  | [] -> [] 
  | (l,SEBconst cb) :: msb -> 
      (try 
	 let vl,recd,msb = factor_fix l cb msb in 
	 let vkn = Array.map (make_kn loc empty_dirpath) vl in
	 let vkn = Array.map long_kn vkn in
	 let ms = extract_msb v all loc msb in 
	 let b = array_exists (in_kn v) vkn in 
	 if all || b then 
	   let d = extract_fixpoint !cur_env vkn recd in 
	   if (not b) && (logical_decl d) then ms 
	   else begin get_decl_references v d;  (l,SEdecl d) :: ms end
	 else ms
       with Impossible ->
	 let ms = extract_msb v all loc msb in 
	 let kn = make_kn loc empty_dirpath l in 
	 let b = in_kn v kn in 
	 if all || b then 
	   let d = extract_constant !cur_env kn cb in
	   if (not b) && (logical_decl d) then ms 
	   else begin get_decl_references v d; (l,SEdecl d) :: ms end
	 else ms)
  | (l,SEBmind mib) :: msb ->
      let ms = extract_msb v all loc msb in
      let kn = make_kn loc empty_dirpath l in 
      let b = in_kn v kn in 
      if all || b then 
	let d = Dind (kn, extract_inductive !cur_env kn) in 
	if (not b) && (logical_decl d) then ms 
	else begin get_decl_references v d; (l,SEdecl d) :: ms end
      else ms
  | (l,SEBmodule mb) :: msb -> 
      let ms = extract_msb v all loc msb in
      let loc = MPdot (loc,l) in 
      if all || in_mp v loc then 
	(l,SEmodule (extract_module v true mb)) :: ms
      else ms
  | (l,SEBmodtype mtb) :: msb ->
      let ms = extract_msb v all loc msb in
      let kn = make_kn loc empty_dirpath l in
      if all || in_kn v kn then 
	(l,SEmodtype (extract_mtb v mtb)) :: ms
      else ms

and extract_meb v all = function 
  | MEBident mp -> MEident mp 
  | MEBapply (meb, meb',_) -> 
      MEapply (extract_meb v true meb, extract_meb v true meb')
  | MEBfunctor (mbid, mtb, meb) -> 
      MEfunctor (mbid, extract_mtb v mtb, extract_meb v true meb)
  | MEBstruct (msid, msb) -> 
      MEstruct (msid, extract_msb v all (MPself msid) msb) 

and extract_module v all mb = 
  { ml_mod_expr = option_app (extract_meb v all) mb.mod_expr;  
    ml_mod_type = (match mb.mod_user_type with 
		     | None -> extract_mtb v mb.mod_type
		     | Some mtb -> extract_mtb v mtb);
    ml_mod_equiv = mb.mod_equiv }
	
and extract_mtb v = function 
  | MTBident kn -> MTident kn 
  | MTBfunsig (mbid, mtb, mtb') -> 
      MTfunsig (mbid, extract_mtb v mtb, extract_mtb v mtb') 
  | MTBsig (msid, msig) -> 
      MTsig (msid, extract_msig v (MPself msid) msig) 
    
and extract_msig v loc = function 
  | [] -> [] 
  | (l,SPBconst cb) :: msig -> 
      let kn = make_kn loc empty_dirpath l in 
      let s = extract_constant_spec !cur_env kn cb in 
      if logical_spec s then extract_msig v loc msig
      else begin
	get_spec_references v s; 
	(l,Spec s) :: (extract_msig v loc msig)
      end
  | (l,SPBmind cb) :: msig -> 
      let kn = make_kn loc empty_dirpath l in 
      let s = Sind (kn, extract_inductive !cur_env kn) in 
      if logical_spec s then extract_msig v loc msig
      else begin 
	get_spec_references v s; 
	(l,Spec s) :: (extract_msig v loc msig)
      end
  | (l,SPBmodule {msb_modtype=mtb}) :: msig -> 
      (l,Smodule (extract_mtb v mtb)) :: (extract_msig v loc msig)
  | (l,SPBmodtype mtb) :: msig -> 
      (l,Smodtype (extract_mtb v mtb)) :: (extract_msig v loc msig)

(* Searching one [ml_decl] in a [ml_structure] by its [kernel_name] *)

let get_decl_in_structure r struc = 
  try 
    let kn = kn_of_r r in 
    let base_mp,ll = labels_of_kn (long_kn kn) in 
    if not (at_toplevel base_mp) then error_not_visible r;
    let sel = List.assoc base_mp struc in
    let rec go ll sel = match ll with 
      | [] -> assert false
      | l :: ll -> 
	  match List.assoc l sel with 
	    | SEdecl d -> d 
	    | SEmodtype m -> assert false
	    | SEmodule m -> 
		match m.ml_mod_expr with 
		  | Some (MEstruct (_,sel)) -> go ll sel 
		  | _ -> error_not_visible r 
    in go ll sel
  with Not_found -> assert false

(*s Extraction in the Coq toplevel. We display the extracted term in
    Ocaml syntax and we use the Coq printers for globals. The
    vernacular command is \verb!Extraction! [qualid]. *)

let unpack = function MEstruct (_,sel) -> sel | _ -> assert false 

let mono_environment refs = 
  let l = environment_until None in 
  init_env l; 
  let v = 
    let kns = List.fold_right (fun r -> KNset.add (kn_of_r r)) refs KNset.empty 
    in let add_mp kn = MPset.union (prefixes_mp (modpath kn)) 
    in { kn = kns; mp = KNset.fold add_mp kns MPset.empty } 
  in 
  List.rev_map (fun (mp,m) -> mp, unpack (extract_meb v false m)) (List.rev l)

let extraction qid = 
  if is_something_opened () then error_section (); 
  let r = Nametab.global qid in 
  if is_custom r then
    msgnl (str "User defined extraction:" ++ spc () ++ 
	   str (find_custom r) ++ fnl ()) 
  else begin 
    let prm = 
      { modular = false; mod_name = id_of_string "Main"; to_appear = [r]} in 
    let kn = kn_of_r r in 
    let struc = optimize_struct prm None (mono_environment [r]) in 
    let d = get_decl_in_structure r struc in 
    print_one_decl struc (long_mp (modpath kn)) d;
    reset_tables ()
  end

(*s Recursive extraction in the Coq toplevel. The vernacular command is
    \verb!Recursive Extraction! [qualid1] ... [qualidn]. We use [extract_env]
    to get the saturated environment to extract. *)

let mono_extraction (f,m) vl = 
  if is_something_opened () then error_section (); 
  let refs = List.map Nametab.global vl in
  let prm = {modular=false; mod_name = m; to_appear= refs} in
  let struc = optimize_struct prm None (mono_environment refs) in 
  print_structure_to_file f prm struc; 
  reset_tables ()

let extraction_rec = mono_extraction (None,id_of_string "Main")

(*s Extraction to a file (necessarily recursive). 
    The vernacular command is 
    \verb!Extraction "file"! [qualid1] ... [qualidn].*)

let lang_suffix () = match lang () with 
  | Ocaml -> ".ml",".mli"
  | Haskell -> ".hs",".hi"
  | Scheme -> ".scm",".scm"
  | Toplevel -> assert false

let filename f = 
  let s,s' = lang_suffix () in
  if Filename.check_suffix f s then 
    let f' = Filename.chop_suffix f s in 
    Some (f,f'^s'),id_of_string f' 
  else Some (f^s,f^s'),id_of_string f

let extraction_file f vl =
  if lang () = Toplevel then error_toplevel () 
  else mono_extraction (filename f) vl

(*s Extraction of a module. The vernacular command is 
  \verb!Extraction Module! [M]. *) 

let module_file_name m = match lang () with 
  | Ocaml -> let f = String.uncapitalize (string_of_id m) in  f^".ml", f^".mli"
  | Haskell -> let f = String.capitalize (string_of_id m) in f^".hs", f^".hi"
  | _ -> assert false

let dir_module_of_id m = 
  try Nametab.full_name_module (make_short_qualid m) 
  with Not_found -> error_unknown_module m

let extraction_module m =
  if is_something_opened () then error_section (); 
  match lang () with 
    | Toplevel -> error_toplevel ()
    | Scheme -> error_scheme ()
    | _ -> 
	let dir_m = dir_module_of_id m in 
	let v = { kn = KNset.empty; mp = MPset.singleton (MPfile dir_m) } in 
	let l = environment_until (Some dir_m) in 
	init_env l;
(* TEMPORARY: make Extraction Module look like Recursive Extraction Module *)
	let struc = 
	  let select l (mp,meb) = 
	    if in_mp v mp then (mp, unpack (extract_meb v true meb)) :: l else l
	  in List.fold_left select [] (List.rev l)
	in 
	let dummy_prm = {modular=true; mod_name=m; to_appear=[]} in
	let struc = optimize_struct dummy_prm None struc in 
	let rec print = function 
	  | [] -> () 
	  | (MPfile dir, _) :: l when dir <> dir_m -> print l 
	  | (MPfile dir, sel) as e :: l -> 
	      let short_m = snd (split_dirpath dir) in
	      let f = module_file_name short_m in 
	      let prm = {modular=true;mod_name=short_m;to_appear=[]} in
	      print_structure_to_file (Some f) prm [e]; 
	      print l 
	  | _ -> assert false
	in print struc; 
	reset_tables ()


(*i	let mp,meb = list_last l in 
	let struc = [mp, unpack (extract_meb v true meb)] in 
	let extern_decls = 
	  let filter kn l = 
	    if base_mp (modpath kn) = mp then l else r_of_kn !cur_env kn :: l 
	  in extract_env (KNset.fold filter v.kn [])
	in 
	let prm = {modular=true; mod_name=m; to_appear=[]} in 
	let struc = optimize_struct prm (Some extern_decls) struc in 
	print_structure_to_file (Some (module_file_name m)) prm struc; 
	reset_tables ()
i*)

	  
(*s Recursive Extraction of all the modules [M] depends on. 
  The vernacular command is \verb!Recursive Extraction Module! [M]. *) 

let recursive_extraction_module m =
  if is_something_opened () then error_section (); 
  match lang () with 
    | Toplevel -> error_toplevel () 
    | Scheme -> error_scheme () 
    | _ -> 
	let dir_m = dir_module_of_id m in 
	let v = { kn = KNset.empty; mp = MPset.singleton (MPfile dir_m) } in 
	let l = environment_until (Some dir_m) in 
	init_env l; 
	let struc = 
	  let select l (mp,meb) = 
	    if in_mp v mp then (mp, unpack (extract_meb v true meb)) :: l else l
	  in List.fold_left select [] (List.rev l)
	in 
	let dummy_prm = {modular=true; mod_name=m; to_appear=[]} in
	let struc = optimize_struct dummy_prm None struc in 
	let rec print = function 
	  | [] -> () 
	  | (MPfile dir, sel) as e :: l -> 
	      let short_m = snd (split_dirpath dir) in
	      let f = module_file_name short_m in 
	      let prm = {modular=true;mod_name=short_m;to_appear=[]} in
	      print_structure_to_file (Some f) prm [e]; 
	      print l 
	  | _ -> assert false
	in print struc; 
	reset_tables ()






