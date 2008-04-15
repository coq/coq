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
	  | "CONSTANT" -> SFBconst (Global.lookup_constant (constant_of_kn kn))
	  | "INDUCTIVE" -> SFBmind (Global.lookup_mind kn) 
	  | "MODULE" -> SFBmodule (Global.lookup_module (MPdot (mp,l)))
	  | "MODULE TYPE" -> 
	      SFBmodtype (Global.lookup_modtype (MPdot (mp,l)))
	  | _ -> failwith "caught"
	in l,seb
    | _ -> failwith "caught"
  in 
  match current_toplevel () with 
    | MPself msid -> SEBstruct (msid, List.rev (map_succeed get_reference seg))
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
	   | (l,SFBconst cb') -> 
	       if check <> check_fix env cb' (j+1) then raise Impossible; 
	       labels.(j+1) <- l; 
	   | _ -> raise Impossible) msb'; 
    labels, recd, msb''
  end

(* From a [structure_body] (i.e. a list of [structure_field_body])
   to specifications. *)

let rec extract_sfb_spec env mp = function 
  | [] -> [] 
  | (l,SFBconst cb) :: msig -> 
      let kn = make_con mp empty_dirpath l in 
      let s = extract_constant_spec env kn cb in 
      let specs = extract_sfb_spec env mp msig in
      if logical_spec s then specs 
      else begin Visit.add_spec_deps s; (l,Spec s) :: specs end
  | (l,SFBmind cb) :: msig -> 
      let kn = make_kn mp empty_dirpath l in 
      let s = Sind (kn, extract_inductive env kn) in 
      let specs = extract_sfb_spec env mp msig in
      if logical_spec s then specs 
      else begin Visit.add_spec_deps s; (l,Spec s) :: specs end
  | (l,SFBmodule mb) :: msig -> 
      let specs = extract_sfb_spec env mp msig in 
      let mtb = Modops.type_of_mb env mb in 
      let spec = extract_seb_spec env (mb.mod_type<>None) mtb in 
      (l,Smodule spec) :: specs
  | (l,SFBmodtype mtb) :: msig -> 
      let specs = extract_sfb_spec env mp msig in
      (l,Smodtype (extract_seb_spec env true(*?*) mtb.typ_expr)) :: specs
  | (l,SFBalias(mp1,_))::msig -> 
      extract_sfb_spec env mp 
	((l,SFBmodule {mod_expr = Some (SEBident mp1);
		      mod_type = None;
		      mod_constraints = Univ.Constraint.empty;
		      mod_alias = Mod_subst.empty_subst;
		      mod_retroknowledge = []})::msig)

(* From [struct_expr_body] to specifications *)


and extract_seb_spec env truetype = function
  | SEBident kn when truetype -> Visit.add_mp kn; MTident kn 
  | SEBwith(mtb',With_definition_body(idl,cb))->
      let mtb''= extract_seb_spec env truetype mtb' in
      (match extract_with_type env cb with (* cb peut contenir des kn  *)
	 | None ->  mtb''
	 | Some (vl,typ) -> MTwith(mtb'',ML_With_type(idl,vl,typ)))
  | SEBwith(mtb',With_module_body(idl,mp,_))-> 
      Visit.add_mp mp;
      MTwith(extract_seb_spec env truetype mtb',
	     ML_With_module(idl,mp))
  | SEBfunctor (mbid, mtb, mtb') -> 
      let mp = MPbound mbid in 
      let env' = Modops.add_module mp (Modops.module_body_of_type mtb) env in
	MTfunsig (mbid, extract_seb_spec env true mtb.typ_expr, 
		  extract_seb_spec env' truetype mtb')
  | SEBstruct (msid, msig) -> 
      let mp = MPself msid in 
      let env' = Modops.add_signature mp msig env in 
	MTsig (msid, extract_sfb_spec env' mp msig) 
  | (SEBapply _|SEBident _ (*when not truetype*)) as mtb -> 
      extract_seb_spec env truetype (Modops.eval_struct env mtb)


(* From a [structure_body] (i.e. a list of [structure_field_body])
   to implementations. 

   NB: when [all=false], the evaluation order of the list is
   important: last to first ensures correct dependencies.
*)

let rec extract_sfb env mp all = function 
  | [] -> [] 
  | (l,SFBconst cb) :: msb -> 
      (try 
	 let vl,recd,msb = factor_fix env l cb msb in 
	 let vc = Array.map (make_con mp empty_dirpath) vl in
	 let ms = extract_sfb env mp all msb in 
	 let b = array_exists Visit.needed_con vc in 
	 if all || b then 
	   let d = extract_fixpoint env vc recd in
	   if (not b) && (logical_decl d) then ms 
	   else begin Visit.add_decl_deps d; (l,SEdecl d) :: ms end
	 else ms
       with Impossible ->
	 let ms = extract_sfb env mp all msb in 
	 let c = make_con mp empty_dirpath l in 
	 let b = Visit.needed_con c in 
	 if all || b then 
	   let d = extract_constant env c cb in
	   if (not b) && (logical_decl d) then ms 
	   else begin Visit.add_decl_deps d; (l,SEdecl d) :: ms end
	 else ms)
  | (l,SFBmind mib) :: msb ->
      let ms = extract_sfb env mp all msb in
      let kn = make_kn mp empty_dirpath l in 
      let b = Visit.needed_kn kn in
      if all || b then 
	let d = Dind (kn, extract_inductive env kn) in 
	if (not b) && (logical_decl d) then ms 
	else begin Visit.add_decl_deps d; (l,SEdecl d) :: ms end
      else ms
  | (l,SFBmodule mb) :: msb -> 
      let ms = extract_sfb env mp all msb in
      let mp = MPdot (mp,l) in 
      if all || Visit.needed_mp mp then 
	(l,SEmodule (extract_module env mp true mb)) :: ms
      else ms
  | (l,SFBmodtype mtb) :: msb ->
      let ms = extract_sfb env mp all msb in
      let mp = MPdot (mp,l) in
       if all || Visit.needed_mp mp then 
	(l,SEmodtype (extract_seb_spec env true(*?*) mtb.typ_expr)) :: ms
      else ms
  | (l,SFBalias (mp1,cst)) :: msb -> 
      let ms = extract_sfb env mp all msb in
      let mp = MPdot (mp,l) in 
      if all || Visit.needed_mp mp then 
	(l,SEmodule (extract_module env mp true 
		       {mod_expr = Some (SEBident mp1);
			mod_type = None;
		        mod_constraints= Univ.Constraint.empty;
			mod_alias = empty_subst;
			mod_retroknowledge = []})) :: ms
      else ms

(* From [struct_expr_body] to implementations *)

and extract_seb env mpo all = function 
  | SEBident mp ->  
      if is_modfile mp && not (modular ()) then error_MPfile_as_mod mp false; 
      Visit.add_mp mp; MEident mp 
  | SEBapply (meb, meb',_) -> 
      MEapply (extract_seb env None true meb, 
	       extract_seb env None true meb')
  | SEBfunctor (mbid, mtb, meb) -> 
      let mp = MPbound mbid in 
      let env' = Modops.add_module mp (Modops.module_body_of_type mtb) env in 
      MEfunctor (mbid, extract_seb_spec env true mtb.typ_expr, 
		 extract_seb env' None true meb)
  | SEBstruct (msid, msb) -> 
      let mp,msb = match mpo with 
	| None -> MPself msid, msb 
	| Some mp -> mp, Modops.subst_structure (map_msid msid mp) msb
      in 
      let env' = Modops.add_signature mp msb env in 
      MEstruct (msid, extract_sfb env' mp all msb) 
  | SEBwith (_,_) -> anomaly "Not available yet"

and extract_module env mp all mb = 
  (* [mb.mod_expr <> None ], since we look at modules from outside. *)
  (* Example of module with empty [mod_expr] is X inside a Module F [X:SIG]. *)
  let meb = Option.get mb.mod_expr in
  let mtb = match mb.mod_type with 
    | None -> Modops.eval_struct env meb 
    | Some mt -> mt 
  in
  (* Because of the "with" construct, the module type can be [MTBsig] with *)
  (* a msid different from the one of the module. Here is the patch. *)
  (* PL 26/02/2008: is this still relevant ?
  let mtb = replicate_msid meb mtb in *)
  { ml_mod_expr = extract_seb env (Some mp) all meb;
    ml_mod_type = extract_seb_spec env (mb.mod_type<>None) mtb }


let unpack = function MEstruct (_,sel) -> sel | _ -> assert false 

let mono_environment refs mpl = 
  Visit.reset ();
  List.iter Visit.add_ref refs; 
  List.iter Visit.add_mp mpl; 
  let env = Global.env () in 
  let l = List.rev (environment_until None) in 
  List.rev_map 
    (fun (mp,m) -> mp, unpack (extract_seb env (Some mp) false m)) l

(**************************************)
(*S Part II : Input/Output primitives *)
(**************************************)

let descr () = match lang () with 
  | Ocaml -> Ocaml.ocaml_descr 
  | Haskell -> Haskell.haskell_descr 
  | Scheme -> Scheme.scheme_descr

(* From a filename string "foo.ml" or "foo", builds "foo.ml" and "foo.mli" 
   Works similarly for the other languages. *)

let default_id = id_of_string "Main"

let mono_filename f = 
  let d = descr () in 
  match f with 
    | None -> None, None, default_id
    | Some f -> 
	let f = 
	  if Filename.check_suffix f d.file_suffix then 
	    Filename.chop_suffix f d.file_suffix 
	  else f
	in
	let id = 
	  if lang () <> Haskell then default_id
	  else try id_of_string (Filename.basename f)
	  with _ -> error "Extraction: provided filename is not a valid identifier"
	in
	Some (f^d.file_suffix), Option.map ((^) f) d.sig_suffix, id

(* Builds a suitable filename from a module id *)

let module_filename m = 
  let d = descr () in 
  let f = if d.capital_file then String.capitalize else String.uncapitalize in 
  let fn = f (string_of_id m) in
  Some (fn^d.file_suffix), Option.map ((^) fn) d.sig_suffix, m

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
  let cout = Option.map open_out fn in 
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
    Option.iter close_out cout; 
  with e -> 
    Option.iter close_out cout; raise e
  end;
  Option.iter info_file fn;
  (* print the signature *)
  Option.iter 
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
    then (mp, unpack (extract_seb env (Some mp) true meb)) :: l 
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
