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

(***************************************)
(*S Part I: computing Coq environment. *)
(***************************************)

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
      (l,Smodule (extract_mtb env mtb)) :: (extract_msig env mp msig)
  | (l,SPBmodtype mtb) :: msig -> 
      (l,Smodtype (extract_mtb env mtb)) :: (extract_msig env mp msig)

and extract_mtb env = function 
  | MTBident kn -> Visit.add_kn kn; MTident kn 
  | MTBfunsig (mbid, mtb, mtb') -> 
      let mp = MPbound mbid in 
      let env' = Modops.add_module mp (Modops.module_body_of_type mtb) env in 
      MTfunsig (mbid, extract_mtb env mtb, 
		extract_mtb env' mtb') 
  | MTBsig (msid, msig) -> 
      let mp = MPself msid in 
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
	(l,SEmodtype (extract_mtb env mtb)) :: ms
      else ms

and extract_meb env mpo all = function 
  | MEBident mp -> 
      if is_modfile mp && not (modular ()) then error_MPfile_as_mod mp false; 
      Visit.add_mp mp; MEident mp 
  | MEBapply (meb, meb',_) -> 
      MEapply (extract_meb env None true meb, 
	       extract_meb env None true meb')
  | MEBfunctor (mbid, mtb, meb) -> 
      let mp = MPbound mbid in 
      let env' = Modops.add_module mp (Modops.module_body_of_type mtb) env in 
      MEfunctor (mbid, extract_mtb env mtb, 
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
    ml_mod_type = extract_mtb env mtb }

let unpack = function MEstruct (_,sel) -> sel | _ -> assert false 

let mono_environment refs mpl = 
  Visit.reset ();
  List.iter Visit.add_ref refs; 
  List.iter Visit.add_mp mpl; 
  let env = Global.env () in 
  let l = List.rev (environment_until None) in 
  List.rev_map 
    (fun (mp,m) -> mp, unpack (extract_meb env (Some mp) false m)) l

(**************************************)
(*S Part II : Input/Output primitives *)
(**************************************)

let descr () = match lang () with 
  | Ocaml -> Ocaml.ocaml_descr 
  | Haskell -> Haskell.haskell_descr 
  | Scheme -> Scheme.scheme_descr

(* From a filename string "foo.ml" or "foo", builds "foo.ml" and "foo.mli" 
   Works similarly for the other languages. *)

let mono_filename f = 
  let d = descr () in 
  match f with 
    | None -> None, None, id_of_string "Main"
    | Some f -> 
	let f = 
	  if Filename.check_suffix f d.file_suffix then 
	    Filename.chop_suffix f d.file_suffix 
	  else f
	in 
	Some (f^d.file_suffix), option_map ((^) f) d.sig_suffix, id_of_string f

(* Builds a suitable filename from a module id *)

let module_filename m = 
  let d = descr () in 
  let f = if d.capital_file then String.capitalize else String.uncapitalize in 
  let fn = f (string_of_id m) in
  Some (fn^d.file_suffix), option_map ((^) fn) d.sig_suffix, m

(*s Extraction of one decl to stdout. *)

let print_one_decl struc mp decl =
  let d = descr () in 
  reset_renaming_tables AllButExternal; 
  ignore (create_renamings struc);
  push_visible mp; 
  msgnl (d.pp_decl decl); 
  pop_visible ()

(*s Extraction of a ml struct to a file. *)

let print_structure_to_file (fn,si,mo) struc =
  let d = descr () in 
  reset_renaming_tables AllButExternal; 
  let used_modules = create_renamings struc in 
  let unsafe_needs = {
    mldummy = struct_ast_search ((=) MLdummy) struc; 
    tdummy = struct_type_search Mlutil.isDummy struc; 
    tunknown = struct_type_search ((=) Tunknown) struc; 
    magic = 
      if lang () <> Haskell then false 
      else struct_ast_search (function MLmagic _ -> true | _ -> false) struc }
  in
  (* print the implementation *)
  let cout = option_map open_out fn in 
  let ft = match cout with 
    | None -> !Pp_control.std_ft
    | Some cout -> Pp_control.with_output_to cout in 
  begin try 
    msg_with ft (d.preamble mo used_modules unsafe_needs);
    if lang () = Ocaml then begin 
      (* for computing objects to duplicate *)
      let devnull = Format.make_formatter (fun _ _ _ -> ()) (fun _ -> ()) in
      msg_with devnull (d.pp_struct struc);
      reset_renaming_tables OnlyLocal; 
    end; 
    msg_with ft (d.pp_struct struc);
    option_iter close_out cout; 
  with e -> 
    option_iter close_out cout; raise e
  end;
  option_iter info_file fn;
  (* print the signature *)
  option_iter 
    (fun si -> 
       let cout = open_out si in
       let ft = Pp_control.with_output_to cout in
       begin try 
	 msg_with ft (d.sig_preamble mo used_modules unsafe_needs);
	 reset_renaming_tables OnlyLocal;
	 msg_with ft (d.pp_sig (signature_of_structure struc));
	 close_out cout;
       with e -> 
	 close_out cout; raise e 
       end; 
       info_file si)
    si


(*********************************************)
(*s Part III: the actual extraction commands *)
(*********************************************)


let reset () =  
  Visit.reset (); reset_tables (); reset_renaming_tables Everything

let init modular = 
  check_inside_section (); check_inside_module ();
  set_keywords (descr ()).keywords;
  set_modular modular;
  reset ();
  if modular && lang () = Scheme then error_scheme ()


(*s Recursive extraction in the Coq toplevel. The vernacular command is
    \verb!Recursive Extraction! [qualid1] ... [qualidn]. Also used when 
    extracting to a file with the command: 
    \verb!Extraction "file"! [qualid1] ... [qualidn]. *)

let full_extraction f qualids = 
  init false; 
  let rec find = function 
    | [] -> [],[]
    | q::l -> 
	let refs,mps = find l in 
	try 
	  let mp = Nametab.locate_module (snd (qualid_of_reference q)) in 
	  if is_modfile mp then error_MPfile_as_mod mp true; 
	  refs,(mp::mps)
	with Not_found -> (Nametab.global q)::refs, mps 
  in  
  let refs,mps = find qualids in
  let struc = optimize_struct refs (mono_environment refs mps) in 
  warning_axioms (); 
  print_structure_to_file (mono_filename f) struc; 
  reset ()


(*s Simple extraction in the Coq toplevel. The vernacular command 
    is \verb!Extraction! [qualid]. *)

let simple_extraction qid = 
  init false; 
  try 
    let mp = Nametab.locate_module (snd (qualid_of_reference qid)) in 
    if is_modfile mp then error_MPfile_as_mod mp true; 
    full_extraction None [qid]
  with Not_found -> 
    let r = Nametab.global qid in 
    if is_custom r then
      msgnl (str "User defined extraction:" ++ spc () ++ 
	       str (find_custom r) ++ fnl ()) 
    else
      let struc = optimize_struct [r] (mono_environment [r] []) in
      let d = get_decl_in_structure r struc in 
      warning_axioms (); 
      print_one_decl struc (modpath_of_r r) d;
      reset ()


(*s (Recursive) Extraction of a library. The vernacular command is 
  \verb!(Recursive) Extraction Library! [M]. *) 

let extraction_library is_rec m =
  init true; 
  let dir_m = 
    let q = make_short_qualid m in 
    try Nametab.full_name_module q with Not_found -> error_unknown_module q
  in 
  Visit.add_mp (MPfile dir_m); 
  let env = Global.env () in	
  let l = List.rev (environment_until (Some dir_m)) in 
  let select l (mp,meb) = 
    if Visit.needed_mp mp 
    then (mp, unpack (extract_meb env (Some mp) true meb)) :: l 
    else l
  in 
  let struc = List.fold_left select [] l in 
  let struc = optimize_struct [] struc in 
  warning_axioms (); 
  record_contents_fstlev struc; 
  let rec print = function 
    | [] -> () 
    | (MPfile dir, _) :: l when not is_rec && dir <> dir_m -> print l 
    | (MPfile dir, sel) as e :: l -> 
	let short_m = snd (split_dirpath dir) in
	print_structure_to_file (module_filename short_m) [e]; 
	print l 
    | _ -> assert false
  in 
  print struc; 
  reset ()





