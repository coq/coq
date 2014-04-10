(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util

(* Dump of globalization (to be used by coqdoc) *)

let glob_file = ref Pervasives.stdout

let open_glob_file f =
  glob_file := Pervasives.open_out f

let close_glob_file () =
  Pervasives.close_out !glob_file

type glob_output_t =
    | NoGlob
    | StdOut
    | MultFiles
    | Feedback
    | File of string

let glob_output = ref NoGlob

let dump () = !glob_output != NoGlob

let noglob () = glob_output := NoGlob

let dump_to_dotglob () = glob_output := MultFiles

let dump_into_file f =
  if String.equal f "stdout" then
    (glob_output := StdOut; glob_file := Pervasives.stdout)
  else
    (glob_output := File f; open_glob_file f)

let feedback_glob () = glob_output := Feedback

let dump_string s =
  if dump () && !glob_output != Feedback then 
    Pervasives.output_string !glob_file s

let start_dump_glob vfile =
  match !glob_output with
  | MultFiles ->
      open_glob_file (Filename.chop_extension vfile ^ ".glob");
      output_string !glob_file "DIGEST ";
      output_string !glob_file (Digest.to_hex (Digest.file vfile));
      output_char !glob_file '\n'
  | File f ->
      open_glob_file f;
      output_string !glob_file "DIGEST NO\n"
  | NoGlob | Feedback | StdOut ->
      ()

let end_dump_glob () =
  match !glob_output with
  | MultFiles | File _ -> close_glob_file ()
  | NoGlob | Feedback | StdOut -> ()

let previous_state = ref MultFiles
let pause () = previous_state := !glob_output; glob_output := NoGlob
let continue () = glob_output := !previous_state

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
    | Globnames.ConstRef cst ->
	type_of_logical_kind (Decls.constant_kind cst)
    | Globnames.VarRef v ->
	"var" ^ type_of_logical_kind (Decls.variable_kind v)
    | Globnames.IndRef ind ->
	let (mib,oib) = Inductive.lookup_mind_specif (Global.env ()) ind in
	  if mib.Declarations.mind_record then
	    if mib.Declarations.mind_finite then "rec"
	    else "corec"
	  else if mib.Declarations.mind_finite then "ind"
	  else "coind"
    | Globnames.ConstructRef _ -> "constr"

let remove_sections dir =
  if Libnames.is_dirpath_prefix_of dir (Lib.cwd ()) then
    (* Not yet (fully) discharged *)
    Libnames.pop_dirpath_n (Lib.sections_depth ()) (Lib.cwd ())
  else
    (* Theorem/Lemma outside its outer section of definition *)
    dir

let interval loc =
  let loc1,loc2 = Loc.unloc loc in
  loc1, loc2-1

let dump_ref loc filepath modpath ident ty =
  if !glob_output = Feedback then
    Pp.feedback (Interface.GlobRef (loc, filepath, modpath, ident, ty))
  else
    let bl,el = interval loc in
    dump_string (Printf.sprintf "R%d:%d %s %s %s %s\n"
		  bl el filepath modpath ident ty)

let dump_reference loc modpath ident ty =
  let filepath = Names.DirPath.to_string (Lib.library_dp ()) in
  dump_ref loc filepath modpath ident ty

let dump_modref loc mp ty =
  let (dp, l) = Lib.split_modpath mp in
  let filepath = Names.DirPath.to_string dp in
  let l = if List.is_empty l then l else List.drop_last l in
  let modpath = Names.DirPath.to_string (Names.DirPath.make l) in
  let ident = "<>" in
  dump_ref loc filepath modpath ident ty

let dump_libref loc dp ty =
  dump_ref loc (Names.DirPath.to_string dp) "<>" "<>" ty

let cook_notation df sc =
  (* We encode notations so that they are space-free and still human-readable *)
  (* - all spaces are replaced by _                                           *)
  (* - all _ denoting a non-terminal symbol are replaced by x                 *)
  (* - all terminal tokens are surrounded by single quotes, including '_'     *)
  (*   which already denotes terminal _                                       *)
  (* - all single quotes in terminal tokens are doubled                       *)
  (* - characters < 32 are represented by '^A, '^B, '^C, etc                  *)
  (* The output is decoded in function Index.prepare_entry of coqdoc          *)
  let ntn = String.make (String.length df * 3) '_' in
  let j = ref 0 in
  let l = String.length df - 1 in
  let i = ref 0 in
  while !i <= l do
    assert (df.[!i] != ' ');
    if df.[!i] == '_' && (Int.equal !i l || df.[!i+1] == ' ') then
      (* Next token is a non-terminal *)
      (ntn.[!j] <- 'x'; incr j; incr i)
    else begin
      (* Next token is a terminal *)
      ntn.[!j] <- '\''; incr j;
      while !i <= l && df.[!i] != ' ' do
	if df.[!i] < ' ' then
	  let c = char_of_int (int_of_char 'A' + int_of_char df.[!i] - 1) in
	  (String.blit ("'^" ^ String.make 1 c) 0 ntn !j 3; j := !j+3; incr i)
	else begin
	  if df.[!i] == '\'' then (ntn.[!j] <- '\''; incr j);
	  ntn.[!j] <- df.[!i]; incr j; incr i
	end
      done;
      ntn.[!j] <- '\''; incr j
    end;
    if !i <= l then (ntn.[!j] <- '_'; incr j; incr i)
  done;
  let df = String.sub ntn 0 !j in
  match sc with Some sc -> ":" ^ sc ^ ":" ^ df | _ -> "::" ^ df

let dump_notation_location posl df (((path,secpath),_),sc) =
  if dump () then
    let path = Names.DirPath.to_string path in
    let secpath = Names.DirPath.to_string secpath in
    let df = cook_notation df sc in
    List.iter (fun l ->
      dump_ref (Loc.make_loc l) path secpath df "not")
      posl

let add_glob_gen loc sp lib_dp ty =
  if dump () then
    let mod_dp,id = Libnames.repr_path sp in
    let mod_dp = remove_sections mod_dp in
    let mod_dp_trunc = Libnames.drop_dirpath_prefix lib_dp mod_dp in
    let filepath = Names.DirPath.to_string lib_dp in
    let modpath = Names.DirPath.to_string mod_dp_trunc in
    let ident = Names.Id.to_string id in
      dump_ref loc filepath modpath ident ty

let add_glob loc ref =
  if dump () && not (Loc.is_ghost loc) then
    let sp = Nametab.path_of_global ref in
    let lib_dp = Lib.library_part ref in
    let ty = type_of_global_ref ref in
      add_glob_gen loc sp lib_dp ty

let mp_of_kn kn =
  let mp,sec,l = Names.repr_kn kn in
    Names.MPdot (mp,l)

let add_glob_kn loc kn =
  if dump () && not (Loc.is_ghost loc) then
    let sp = Nametab.path_of_syndef kn in
    let lib_dp = Lib.dp_of_mp (mp_of_kn kn) in
      add_glob_gen loc sp lib_dp "syndef"

let dump_binding loc id = ()

let dump_def ty loc secpath id =
  if !glob_output = Feedback then
    Pp.feedback (Interface.GlobDef (loc, id, secpath, ty))
  else
    let bl,el = interval loc in
    dump_string (Printf.sprintf "%s %d:%d %s %s\n" ty bl el secpath id)

let dump_definition (loc, id) sec s =
  dump_def s loc (Names.DirPath.to_string (Lib.current_dirpath sec)) (Names.Id.to_string id)

let dump_constraint ((loc, n), _, _) sec ty =
  match n with
    | Names.Name id -> dump_definition (loc, id) sec ty
    | Names.Anonymous -> ()

let dump_moddef loc mp ty =
  let (dp, l) = Lib.split_modpath mp in
  let mp = Names.DirPath.to_string (Names.DirPath.make l) in
  dump_def ty loc "<>" mp

let dump_notation (loc,(df,_)) sc sec =
  (* We dump the location of the opening '"' *)
  let i = fst (Loc.unloc loc) in
  let location = (Loc.make_loc (i, i+1)) in
  dump_def "not" location (Names.DirPath.to_string (Lib.current_dirpath sec)) (cook_notation df sc)

