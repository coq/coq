(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)


let rec drop_last = function [] -> assert false | hd :: [] -> [] | hd :: tl -> hd :: drop_last tl

(* Dump of globalization (to be used by coqdoc) *)

let glob_file = ref Pervasives.stdout

let open_glob_file f =
  glob_file := Pervasives.open_out f
  
let close_glob_file () =
  Pervasives.close_out !glob_file

let dump_string s = 
  Pervasives.output_string !glob_file s

type glob_output_t = 
    | NoGlob
    | StdOut
    | MultFiles
    | File of string

let glob_output = ref NoGlob

let dump () = !glob_output != NoGlob

let noglob () = glob_output := NoGlob

let dump_to_stdout () = glob_output := StdOut; glob_file := Pervasives.stdout

let multi_dump () = !glob_output = MultFiles

let dump_to_dotglob f = glob_output := MultFiles

let dump_into_file f = glob_output := File f; open_glob_file f


let previous_state = ref MultFiles
let pause () = previous_state := !glob_output
let continue () = glob_output := !previous_state


let token_number = ref 0
let last_pos = ref 0

type coqdoc_state = Lexer.location_table * int * int

let coqdoc_freeze () =
  let lt = Lexer.location_table() in
  let state = (lt,!token_number,!last_pos) in
    token_number := 0;
    last_pos := 0;
    state

let coqdoc_unfreeze (lt,tn,lp) =
  Lexer.restore_location_table lt;
  token_number := tn;
  last_pos := lp

open Decl_kinds

let type_of_logical_kind = function
  | IsDefinition def -> 
      (match def with
      | Definition -> "def"
      | Coercion -> "coe"
      | SubClass -> "subclass"
      | CanonicalStructure -> "canonstruc"
      | Example -> "ex"
      | Fixpoint -> "def"
      | CoFixpoint -> "def"
      | Scheme -> "scheme"
      | StructureComponent -> "proj"
      | IdentityCoercion -> "coe"
      | Instance -> "inst"
      | Method -> "meth")
  | IsAssumption a ->
      (match a with
      | Definitional -> "defax"
      | Logical -> "prfax"
      | Conjectural -> "prfax")
  | IsProof th ->
      (match th with
      | Theorem
      | Lemma
      | Fact
      | Remark
      | Property
      | Proposition
      | Corollary -> "thm")

let type_of_global_ref gr =
  if Typeclasses.is_class gr then
    "class"
  else
    match gr with
    | Libnames.ConstRef cst -> 
	type_of_logical_kind (Decls.constant_kind cst)
    | Libnames.VarRef v ->
	"var" ^ type_of_logical_kind (Decls.variable_kind v)
    | Libnames.IndRef ind ->
	let (mib,oib) = Inductive.lookup_mind_specif (Global.env ()) ind in
	  if mib.Declarations.mind_record then
	    if mib.Declarations.mind_finite then "rec"
	    else "corec"
	  else if mib.Declarations.mind_finite then "ind"
	  else "coind"
    | Libnames.ConstructRef _ -> "constr"

let remove_sections dir =
  if Libnames.is_dirpath_prefix_of dir (Lib.cwd ()) then
    (* Not yet (fully) discharged *)
    Libnames.extract_dirpath_prefix (Lib.sections_depth ()) (Lib.cwd ())
  else
    (* Theorem/Lemma outside its outer section of definition *)
    dir

let dump_ref loc filepath modpath ident ty =
  dump_string (Printf.sprintf "R%d %s %s %s %s\n" 
		  (fst (Util.unloc loc)) filepath modpath ident ty)

let add_glob_gen loc sp lib_dp ty =
  let mod_dp,id = Libnames.repr_path sp in
  let mod_dp = remove_sections mod_dp in
  let mod_dp_trunc = Libnames.drop_dirpath_prefix lib_dp mod_dp in
  let filepath = Names.string_of_dirpath lib_dp in
  let modpath = Names.string_of_dirpath mod_dp_trunc in
  let ident = Names.string_of_id id in
    dump_ref loc filepath modpath ident ty

let add_glob loc ref = 
  if loc <> Util.dummy_loc then
    let sp = Nametab.sp_of_global ref in
    let lib_dp = Lib.library_part ref in
    let ty = type_of_global_ref ref in
      add_glob_gen loc sp lib_dp ty
      
let mp_of_kn kn = 
  let mp,sec,l = Names.repr_kn kn in 
    Names.MPdot (mp,l) 

let add_glob_kn loc kn =
  if loc <> Util.dummy_loc then
    let sp = Nametab.sp_of_syntactic_definition kn in
    let lib_dp = Lib.dp_of_mp (mp_of_kn kn) in
      add_glob_gen loc sp lib_dp "syndef"

let add_local loc id = ()
(*   let mod_dp,id = repr_path sp in *)
(*   let mod_dp = remove_sections mod_dp in *)
(*   let mod_dp_trunc = drop_dirpath_prefix lib_dp mod_dp in *)
(*   let filepath = string_of_dirpath lib_dp in *)
(*   let modpath = string_of_dirpath mod_dp_trunc in *)
(*   let ident = string_of_id id in *)
(*     dump_string (Printf.sprintf "R%d %s %s %s %s\n"  *)
(* 		    (fst (unloc loc)) filepath modpath ident ty) *)

let dump_binding loc id = ()
      
(* BEGIN obsolete *)

let dump_modref qid = Pp.warning ("Dumpglob.modref: not yet implemented")
  
let dump_def loc ref = 
  let curr_mp, _ = Lib.current_prefix() in
  let lib_dp, curr_dp = Lib.split_mp curr_mp in
  let mod_dp_trunc =  Libnames.drop_dirpath_prefix lib_dp curr_dp in

  let fullname = Libnames.string_of_qualid (Libnames.make_qualid mod_dp_trunc ref) in
  let filepath = Names.string_of_dirpath lib_dp in
    dump_string (Printf.sprintf "D%d %s %s\n" (fst (Util.unloc loc)) filepath fullname)

(* END obsolete *)

let dump_definition (loc, id) sec s =
  dump_string (Printf.sprintf "%s %d %s %s\n" s (fst (Util.unloc loc)) 
			(Names.string_of_dirpath (Lib.current_dirpath sec)) (Names.string_of_id id))
    
let dump_reference loc modpath ident ty =
  dump_string (Printf.sprintf "R%d %s %s %s %s\n" 
		  (fst (Util.unloc loc)) (Names.string_of_dirpath (Lib.library_dp ())) modpath ident ty)

let dump_constraint ((loc, n), _, _) sec ty =
  match n with
    | Names.Name id -> dump_definition (loc, id) sec ty
    | Names.Anonymous -> ()

let dump_name (loc, n) sec ty =
  match n with
  | Names.Name id -> dump_definition (loc, id) sec ty
  | Names.Anonymous -> ()

let dump_local_binder b sec ty =
  match b with
  | Topconstr.LocalRawAssum (nl, _, _) -> 
      List.iter (fun x -> dump_name x sec ty) nl
  | Topconstr.LocalRawDef _ -> ()

let dump_modref loc mp ty =
  let (dp, l) = Lib.split_modpath mp in
  let fp = Names.string_of_dirpath dp in
  let mp = Names.string_of_dirpath (Names.make_dirpath (drop_last l)) in
    dump_string (Printf.sprintf "R%d %s %s %s %s\n" 
		    (fst (Util.unloc loc)) fp mp "<>" ty)

let dump_moddef loc mp ty =
  let (dp, l) = Lib.split_modpath mp in
  let mp = Names.string_of_dirpath (Names.make_dirpath l) in
    dump_string (Printf.sprintf "%s %d %s %s\n" ty (fst (Util.unloc loc)) "<>" mp)

let dump_libref loc dp ty =
  dump_string (Printf.sprintf "R%d %s <> <> %s\n" 
		  (fst (Util.unloc loc)) (Names.string_of_dirpath dp) ty)

let dump_notation_location pos ((path,df),sc) =
  let rec next growing =
    let loc = Lexer.location_function !token_number in
    let (bp,_) = Util.unloc loc in
      if growing then if bp >= pos then loc else (incr token_number; next true)
      else if bp = pos then loc
      else if bp > pos then (decr token_number;next false)
      else (incr token_number;next true) in
  let loc = next (pos >= !last_pos) in
    last_pos := pos;
    let path = Names.string_of_dirpath path in
    let _sc = match sc with Some sc -> " "^sc | _ -> "" in
      dump_string (Printf.sprintf "R%d %s \"%s\" not\n" (fst (Util.unloc loc)) path df)


