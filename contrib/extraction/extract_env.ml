(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
open Modutil
open Common
open Mod_subst

(*s Obtaining Coq environment. *)

let toplevel_env () = 
  let seg = Lib.contents_after None in 
  let get_reference = function 
    | (_,kn), Lib.Leaf o ->
	let mp,_,l = repr_kn kn in 
	let seb = match Libobject.object_tag o with
	  | "CONSTANT" -> SEBconst (Global.lookup_constant (constant_of_kn kn))
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


(*s Visit: 
  a structure recording the needed dependencies for the current extraction *)

module type VISIT = sig 
  (* Reset the dependencies by emptying the visit lists *)
  val reset : unit -> unit
    
  (* Add the module_path and all its prefixes to the mp visit list *)  
  val add_mp : module_path -> unit
    
  (* Add kernel_name / constant / reference / ... in the visit lists. 
     These functions silently add the mp of their arg in the mp list *)
  val add_kn : kernel_name -> unit
  val add_con : constant -> unit
  val add_ref : global_reference -> unit
  val add_decl_deps : ml_decl -> unit
  val add_spec_deps : ml_spec -> unit

  (* Test functions: 
     is a particular object a needed dependency for the current extraction ? *)
  val needed_kn : kernel_name -> bool 
  val needed_con : constant -> bool
  val needed_mp : module_path -> bool
end
  
module Visit : VISIT = struct 
  (* Thanks to C.S.C, what used to be in a single KNset should now be split 
     into a KNset (for inductives and modules names) and a Cset for constants 
     (and still the remaining MPset) *)
  type must_visit = 
      { mutable kn : KNset.t; mutable con : Cset.t; mutable mp : MPset.t }
  (* the imperative internal visit lists *)
  let v = { kn = KNset.empty ; con = Cset.empty ; mp = MPset.empty } 
  (* the accessor functions *)
  let reset () = v.kn <- KNset.empty; v.con <- Cset.empty; v.mp <- MPset.empty
  let needed_kn kn = KNset.mem kn v.kn
  let needed_con c = Cset.mem c v.con
  let needed_mp mp = MPset.mem mp v.mp
  let add_mp mp = 
    check_loaded_modfile mp; v.mp <- MPset.union (prefixes_mp mp) v.mp
  let add_kn kn = v.kn <- KNset.add kn v.kn; add_mp (modpath kn)
  let add_con c = v.con <- Cset.add c v.con; add_mp (con_modpath c)
  let add_ref = function 
    | ConstRef c -> add_con c
    | IndRef (kn,_) | ConstructRef ((kn,_),_) -> add_kn kn
    | VarRef _ -> assert false
  let add_decl_deps = decl_iter_references add_ref add_ref add_ref 
  let add_spec_deps = spec_iter_references add_ref add_ref add_ref
end

exception Impossible

let check_arity env cb = 
  let t = Typeops.type_of_constant_type env cb.const_type in
  if Reduction.is_arity env t then raise Impossible

let check_fix env cb i = 
  match cb.const_body with 
    | None -> raise Impossible
    | Some lbody -> 
	match kind_of_term (Declarations.force lbody) with 
	  | Fix ((_,j),recd) when i=j -> check_arity env cb; (true,recd)
	  | CoFix (j,recd) when i=j -> check_arity env cb; (false,recd)
	  | _ -> raise Impossible

let factor_fix env l cb msb = 
  let _,recd as check = check_fix env cb 0 in 
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
	       if check <> check_fix env cb' (j+1) then raise Impossible; 
	       labels.(j+1) <- l; 
	   | _ -> raise Impossible) msb'; 
    labels, recd, msb''
  end

let rec extract_msig env mp = function 
  | [] -> [] 
  | (l,SPBconst cb) :: msig -> 
      let kn = make_con mp empty_dirpath l in 
      let s = extract_constant_spec env kn cb in 
      if logical_spec s then extract_msig env mp msig
      else begin
	Visit.add_spec_deps s;
	(l,Spec s) :: (extract_msig env mp msig)
      end
  | (l,SPBmind cb) :: msig -> 
      let kn = make_kn mp empty_dirpath l in 
      let s = Sind (kn, extract_inductive env kn) in 
      if logical_spec s then extract_msig env mp msig
      else begin 
	Visit.add_spec_deps s;
	(l,Spec s) :: (extract_msig env mp msig)
      end
  | (l,SPBmodule {msb_modtype=mtb}) :: msig -> 
      (l,Smodule (extract_mtb env None mtb)) :: (extract_msig env mp msig)
  | (l,SPBmodtype mtb) :: msig -> 
      (l,Smodtype (extract_mtb env None mtb)) :: (extract_msig env mp msig)

and extract_mtb env mpo = function 
  | MTBident kn -> Visit.add_kn kn; MTident kn 
  | MTBfunsig (mbid, mtb, mtb') -> 
      let mp = MPbound mbid in 
      let env' = Modops.add_module mp (Modops.module_body_of_type mtb) env in 
      MTfunsig (mbid, extract_mtb env None mtb, 
		extract_mtb env' None mtb') 
  | MTBsig (msid, msig) -> 
      let mp, msig = match mpo with 
	| None -> MPself msid, msig
	| Some mp -> mp, Modops.subst_signature_msid msid mp msig
      in
      let env' = Modops.add_signature mp msig env in 
      MTsig (msid, extract_msig env' mp msig) 

let rec extract_msb env mp all = function 
  | [] -> [] 
  | (l,SEBconst cb) :: msb -> 
      (try 
	 let vl,recd,msb = factor_fix env l cb msb in 
	 let vc = Array.map (make_con mp empty_dirpath) vl in
	 let ms = extract_msb env mp all msb in 
	 let b = array_exists Visit.needed_con vc in 
	 if all || b then 
	   let d = extract_fixpoint env vc recd in
	   if (not b) && (logical_decl d) then ms 
	   else begin Visit.add_decl_deps d; (l,SEdecl d) :: ms end
	 else ms
       with Impossible ->
	 let ms = extract_msb env mp all msb in 
	 let c = make_con mp empty_dirpath l in 
	 let b = Visit.needed_con c in 
	 if all || b then 
	   let d = extract_constant env c cb in
	   if (not b) && (logical_decl d) then ms 
	   else begin Visit.add_decl_deps d; (l,SEdecl d) :: ms end
	 else ms)
  | (l,SEBmind mib) :: msb ->
      let ms = extract_msb env mp all msb in
      let kn = make_kn mp empty_dirpath l in 
      let b = Visit.needed_kn kn in
      if all || b then 
	let d = Dind (kn, extract_inductive env kn) in 
	if (not b) && (logical_decl d) then ms 
	else begin Visit.add_decl_deps d; (l,SEdecl d) :: ms end
      else ms
  | (l,SEBmodule mb) :: msb -> 
      let ms = extract_msb env mp all msb in
      let mp = MPdot (mp,l) in 
      if all || Visit.needed_mp mp then 
	(l,SEmodule (extract_module env mp true mb)) :: ms
      else ms
  | (l,SEBmodtype mtb) :: msb ->
      let ms = extract_msb env mp all msb in
      let kn = make_kn mp empty_dirpath l in
      if all || Visit.needed_kn kn then 
	(l,SEmodtype (extract_mtb env None mtb)) :: ms
      else ms

and extract_meb env mpo all = function 
  | MEBident (MPfile d) -> error_MPfile_as_mod d (* temporary (I hope) *)
  | MEBident mp -> Visit.add_mp mp; MEident mp 
  | MEBapply (meb, meb',_) -> 
      MEapply (extract_meb env None true meb, 
	       extract_meb env None true meb')
  | MEBfunctor (mbid, mtb, meb) -> 
      let mp = MPbound mbid in 
      let env' = Modops.add_module mp (Modops.module_body_of_type mtb) env in 
      MEfunctor (mbid, extract_mtb env None mtb, 
		 extract_meb env' None true meb)
  | MEBstruct (msid, msb) -> 
      let mp,msb = match mpo with 
	| None -> MPself msid, msb 
	| Some mp -> mp, subst_msb (map_msid msid mp) msb
      in 
      let env' = add_structure mp msb env in 
      MEstruct (msid, extract_msb env' mp all msb) 

and extract_module env mp all mb = 
  (* [mb.mod_expr <> None ], since we look at modules from outside. *)
  (* Example of module with empty [mod_expr] is X inside a Module F [X:SIG]. *)
  let meb = out_some mb.mod_expr in
  let mtb = match mb.mod_user_type with None -> mb.mod_type | Some mt -> mt in
  (* Because of the "with" construct, the module type can be [MTBsig] with *)
  (* a msid different from the one of the module. Here is the patch. *)
  let mtb = replicate_msid meb mtb in
  { ml_mod_expr = extract_meb env (Some mp) all meb;
    ml_mod_type = extract_mtb env None mtb }

let unpack = function MEstruct (_,sel) -> sel | _ -> assert false 

let mono_environment refs mpl = 
  Visit.reset ();
  List.iter Visit.add_ref refs; 
  List.iter Visit.add_mp mpl; 
  let env = Global.env () in 
  let l = List.rev (environment_until None) in 
  List.rev_map 
    (fun (mp,m) -> mp, unpack (extract_meb env (Some mp) false m)) l

    
(*s Recursive extraction in the Coq toplevel. The vernacular command is
    \verb!Recursive Extraction! [qualid1] ... [qualidn]. We use [extract_env]
    to get the saturated environment to extract. *)

let mono_extraction (f,m) qualids = 
  check_inside_section (); 
  check_inside_module ();
  let rec find = function 
    | [] -> [],[]
    | q::l -> 
	let refs,mps = find l in 
	try 
	  let mp = Nametab.locate_module (snd (qualid_of_reference q))
	  in refs,(mp::mps)
	with Not_found -> (Nametab.global q)::refs, mps 
  in 	    
  let refs,mps = find qualids in
  let prm = {modular=false; mod_name = m; to_appear= refs} in
  let struc = optimize_struct prm None (mono_environment refs mps) in 
  print_structure_to_file f prm struc; 
  Visit.reset ();
  reset_tables ()

let extraction_rec = mono_extraction (None,id_of_string "Main")

(*s Extraction in the Coq toplevel. We display the extracted term in
    Ocaml syntax and we use the Coq printers for globals. The
    vernacular command is \verb!Extraction! [qualid]. *)

let extraction qid = 
  check_inside_section (); 
  check_inside_module ();
  try 
    let _ = Nametab.locate_module (snd (qualid_of_reference qid)) in 
    extraction_rec [qid]
  with Not_found -> 
    let r = Nametab.global qid in 
    if is_custom r then
      msgnl (str "User defined extraction:" ++ spc () ++ 
	       str (find_custom r) ++ fnl ()) 
    else
      let prm = 
	{ modular = false; mod_name = id_of_string "Main"; to_appear = [r]} in
      let struc = optimize_struct prm None (mono_environment [r] []) in 
      let d = get_decl_in_structure r struc in 
      print_one_decl struc (modpath_of_r r) d;
      Visit.reset (); 
      reset_tables () 

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

(*s Extraction of a module at the toplevel. *)

let extraction_module m = 
  check_inside_section (); 
  check_inside_module ();
  begin match lang () with 
    | Toplevel -> error_toplevel ()
    | Scheme -> error_scheme ()
    | _ -> ()
  end; 
  let q = snd (qualid_of_reference m) in 
  let mp = 
    try Nametab.locate_module q with Not_found -> error_unknown_module q
  in 
  let b = is_modfile mp in 
  let prm = {modular=b; mod_name = id_of_string ""; to_appear= []} in
  Visit.reset ();
  Visit.add_mp mp; 
  let env = Global.env () in 
  let l = List.rev (environment_until None) in 
  let struc = 
    List.rev_map (fun (mp,m) -> mp, unpack (extract_meb env (Some mp) b m)) l
  in
  let struc = optimize_struct prm None struc in 
  let struc = 
    let bmp = base_mp mp in 
    try [bmp, List.assoc bmp struc] with Not_found -> assert false
  in
  print_structure_to_file None prm struc; 
  Visit.reset (); 
  reset_tables ()


(*s (Recursive) Extraction of a library. The vernacular command is 
  \verb!(Recursive) Extraction Library! [M]. *) 

let module_file_name m = match lang () with 
  | Ocaml -> let f = String.uncapitalize (string_of_id m) in  f^".ml", f^".mli"
  | Haskell -> let f = String.capitalize (string_of_id m) in f^".hs", f^".hi"
  | _ -> assert false

let dir_module_of_id m = 
  let q = make_short_qualid m in 
  try Nametab.full_name_module q with Not_found -> error_unknown_module q

let extraction_library is_rec m =
  check_inside_section (); 
  check_inside_module ();  
  begin match lang () with 
    | Toplevel -> error_toplevel ()
    | Scheme -> error_scheme ()
    | _ -> () 
  end; 
  let dir_m = dir_module_of_id m in 
  Visit.reset (); 
  Visit.add_mp (MPfile dir_m); 
  let env = Global.env () in	
  let l = List.rev (environment_until (Some dir_m)) in 
  let select l (mp,meb) = 
    if Visit.needed_mp mp 
    then (mp, unpack (extract_meb env (Some mp) true meb)) :: l 
    else l
  in 
  let struc = List.fold_left select [] l in 
  let dummy_prm = {modular=true; mod_name=m; to_appear=[]} in
  let struc = optimize_struct dummy_prm None struc in 
  let rec print = function 
    | [] -> () 
    | (MPfile dir, _) :: l when not is_rec && dir <> dir_m -> print l 
    | (MPfile dir, sel) as e :: l -> 
	let short_m = snd (split_dirpath dir) in
	let f = module_file_name short_m in 
	let prm = {modular=true;mod_name=short_m;to_appear=[]} in
	print_structure_to_file (Some f) prm [e]; 
	print l 
    | _ -> assert false
  in 
  print struc; 
  Visit.reset ();
  reset_tables ()





