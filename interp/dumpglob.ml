(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


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
    | File of string

let glob_output = ref NoGlob

let dump () = !glob_output != NoGlob

let noglob () = glob_output := NoGlob

let dump_to_stdout () = glob_output := StdOut; glob_file := Pervasives.stdout

let multi_dump () = !glob_output = MultFiles

let dump_to_dotglob f = glob_output := MultFiles

let dump_into_file f = glob_output := File f; open_glob_file f

let dump_string s =
  if dump () then Pervasives.output_string !glob_file s


let previous_state = ref MultFiles
let pause () = previous_state := !glob_output; glob_output := NoGlob
let continue () = glob_output := !previous_state

type coqdoc_state = Lexer.location_table

let coqdoc_freeze = Lexer.location_table
let coqdoc_unfreeze = Lexer.restore_location_table

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
    Libnames.pop_dirpath_n (Lib.sections_depth ()) (Lib.cwd ())
  else
    (* Theorem/Lemma outside its outer section of definition *)
    dir

let dump_ref loc filepath modpath ident ty =
  dump_string (Printf.sprintf "R%d %s %s %s %s\n"
		  (fst (Util.unloc loc)) filepath modpath ident ty)

let add_glob_gen loc sp lib_dp ty =
  if dump () then
    let mod_dp,id = Libnames.repr_path sp in
    let mod_dp = remove_sections mod_dp in
    let mod_dp_trunc = Libnames.drop_dirpath_prefix lib_dp mod_dp in
    let filepath = Names.string_of_dirpath lib_dp in
    let modpath = Names.string_of_dirpath mod_dp_trunc in
    let ident = Names.string_of_id id in
      dump_ref loc filepath modpath ident ty

let add_glob loc ref =
  if dump () && loc <> Util.dummy_loc then
    let sp = Nametab.path_of_global ref in
    let lib_dp = Lib.library_part ref in
    let ty = type_of_global_ref ref in
      add_glob_gen loc sp lib_dp ty

let mp_of_kn kn =
  let mp,sec,l = Names.repr_kn kn in
    Names.MPdot (mp,l)

let add_glob_kn loc kn =
  if dump () && loc <> Util.dummy_loc then
    let sp = Nametab.path_of_syndef kn in
    let lib_dp = Lib.dp_of_mp (mp_of_kn kn) in
      add_glob_gen loc sp lib_dp "syndef"

let dump_binding loc id = ()

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

let dump_modref loc mp ty =
  if dump () then
    let (dp, l) = Lib.split_modpath mp in
    let l = if l = [] then l else Util.list_drop_last l in
    let fp = Names.string_of_dirpath dp in
    let mp = Names.string_of_dirpath (Names.make_dirpath l) in
      dump_string (Printf.sprintf "R%d %s %s %s %s\n"
		      (fst (Util.unloc loc)) fp mp "<>" ty)

let dump_moddef loc mp ty =
  if dump () then
    let (dp, l) = Lib.split_modpath mp in
    let mp = Names.string_of_dirpath (Names.make_dirpath l) in
      dump_string (Printf.sprintf "%s %d %s %s\n" ty (fst (Util.unloc loc)) "<>" mp)

let dump_libref loc dp ty =
  dump_string (Printf.sprintf "R%d %s <> <> %s\n"
		  (fst (Util.unloc loc)) (Names.string_of_dirpath dp) ty)

let cook_notation df sc =
  let ntn = String.make (String.length df * 3) '_' in
  let j = ref 0 in
  let quoted = ref false in
  for i = 0 to String.length df - 1 do
    if df.[i] = '\'' then quoted := not !quoted;
    if df.[i] = ' ' then (ntn.[!j] <- '_'; incr j) else
    if df.[i] = '_' && not !quoted then (ntn.[!j] <- 'x'; incr j) else
    if df.[i] = 'x' && not !quoted then (String.blit "'x'" 0 ntn !j 3; j := !j + 3) else
    (ntn.[!j] <- df.[i]; incr j)
  done;
  let df = String.sub ntn 0 !j in
  match sc with Some sc -> ":" ^ sc ^ ":" ^ df | _ -> "::" ^ df

let dump_notation (loc,(df,_)) sc sec =
  (* We dump the location of the opening '"' *)
  dump_string (Printf.sprintf "not %d %s %s\n" (fst (Util.unloc loc))
    (Names.string_of_dirpath (Lib.current_dirpath sec)) (cook_notation df sc))

let dump_notation_location posl df (((path,secpath),_),sc) =
  if dump () then
    let path = Names.string_of_dirpath path in
    let secpath = Names.string_of_dirpath secpath in
    let df = cook_notation df sc in
    List.iter (fun (bl,el) ->
      dump_string(Printf.sprintf "R%d:%d %s %s %s not\n" bl el path secpath df))
      posl
