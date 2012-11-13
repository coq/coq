(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Term
open Declarations
open Libobject
open Environ
open Pattern
open Matching
open Printer
open Libnames
open Globnames
open Nametab

type filter_function = global_reference -> env -> constr -> bool
type display_function = global_reference -> env -> constr -> unit

module SearchBlacklist =
  Goptions.MakeStringTable
    (struct
      let key = ["Search";"Blacklist"]
      let title = "Current search blacklist : "
      let member_message s b =
	str ("Search blacklist does "^(if b then "" else "not ")^"include "^s)
      let synchronous = true
     end)

(* The functions print_constructors and crible implement the behavior needed
   for the Coq searching commands.
   These functions take as first argument the procedure
   that will be called to treat each entry.  This procedure receives the name
   of the object, the assumptions that will make it possible to print its type,
   and the constr term that represent its type. *)

let print_constructors indsp fn env nconstr =
  for i = 1 to nconstr do
    fn (ConstructRef (indsp,i)) env (Inductiveops.type_of_constructor env (indsp,i))
  done

let rec head_const c = match kind_of_term c with
  | Prod (_,_,d) -> head_const d
  | LetIn (_,_,_,d) -> head_const d
  | App (f,_)   -> head_const f
  | Cast (d,_,_)   -> head_const d
  | _            -> c

(* General search, restricted to head constant if [only_head] *)

let gen_crible refopt (fn : global_reference -> env -> constr -> unit) =
  let env = Global.env () in
  let crible_rec (sp,kn) lobj = match object_tag lobj with
    | "VARIABLE" ->
	(try
	   let (id,_,typ) = Global.lookup_named (basename sp) in
           if refopt = None
	     || head_const typ = constr_of_global (Option.get refopt)
	   then
	     fn (VarRef id) env typ
	 with Not_found -> (* we are in a section *) ())
    | "CONSTANT" ->
	let cst = Global.constant_of_delta_kn kn in
	let typ = Typeops.type_of_constant env cst in
        if refopt = None
	  || head_const typ = constr_of_global (Option.get refopt)
	then
	  fn (ConstRef cst) env typ
    | "INDUCTIVE" ->
	let mind = Global.mind_of_delta_kn kn in
        let mib = Global.lookup_mind mind in
        (match refopt with
	  | Some (IndRef ((kn',tyi) as ind)) when eq_mind mind kn' ->
	      print_constructors ind fn env
	        (Array.length (mib.mind_packets.(tyi).mind_user_lc))
          | Some _ -> ()
	  | _ ->
              Array.iteri
	        (fun i mip -> print_constructors (mind,i) fn env
	          (Array.length mip.mind_user_lc)) mib.mind_packets)
    | _ -> ()
  in
  try
    Declaremods.iter_all_segments crible_rec
  with Not_found ->
    ()

let crible ref = gen_crible (Some ref)

(* Fine Search. By Yves Bertot. *)

let rec head c =
  let c = strip_outer_cast c in
  match kind_of_term c with
  | Prod (_,_,c) -> head c
  | LetIn (_,_,_,c) -> head c
  | _              -> c

let xor a b = (a or b) & (not (a & b))

let plain_display accu ref a c =
  let pc = pr_lconstr_env a c in
  let pr = pr_global ref in
  accu := hov 2 (pr ++ str":" ++ spc () ++ pc) :: !accu

let format_display l = prlist_with_sep fnl (fun x -> x) (List.rev l)

let filter_by_module (module_list:dir_path list) (accept:bool)
  (ref:global_reference) _ _ =
    let sp = path_of_global ref in
    let sl = dirpath sp in
    let rec filter_aux = function
      | m :: tl -> (not (is_dirpath_prefix_of m sl)) && (filter_aux tl)
      | [] -> true
    in
    xor accept (filter_aux module_list)

let ref_eq = Globnames.encode_mind Coqlib.logic_module (id_of_string "eq"), 0
let c_eq = mkInd ref_eq
let gref_eq = IndRef ref_eq

let mk_rewrite_pattern1 eq pattern =
  PApp (PRef eq, [| PMeta None; pattern; PMeta None |])

let mk_rewrite_pattern2 eq pattern =
  PApp (PRef eq, [| PMeta None; PMeta None; pattern |])

let pattern_filter pat _ a c =
  try
    try
      is_matching pat (head c)
    with _ ->
      is_matching
	pat (head (Typing.type_of (Global.env()) Evd.empty c))
    with UserError _ ->
      false

let filtered_search filter_function display_function ref =
  crible ref
    (fun s a c -> if filter_function s a c then display_function s a c)

let rec id_from_pattern = function
  | PRef gr -> gr
(* should be appear as a PRef (VarRef sp) !!
  | PVar id -> Nametab.locate (make_qualid [] (string_of_id id))
 *)
  | PApp (p,_) -> id_from_pattern p
  | _ -> error "The pattern is not simple enough."

let raw_pattern_search extra_filter display_function pat =
  let name = id_from_pattern pat in
  filtered_search
    (fun s a c -> (pattern_filter pat s a c) & extra_filter s a c)
    display_function name

let raw_search_rewrite extra_filter display_function pattern =
  filtered_search
    (fun s a c ->
       ((pattern_filter (mk_rewrite_pattern1 gref_eq pattern) s a c) ||
        (pattern_filter (mk_rewrite_pattern2 gref_eq pattern) s a c))
       && extra_filter s a c)
    display_function gref_eq

let raw_search_by_head extra_filter display_function pattern =
  Errors.todo "raw_search_by_head"

let name_of_reference ref = string_of_id (basename_of_global ref)

let full_name_of_reference ref =
  let (dir,id) = repr_path (path_of_global ref) in
  string_of_dirpath dir ^ "." ^ string_of_id id

(*
 * functions to use the new Libtypes facility
 *)

let raw_search search_function extra_filter display_function pat =
  let env = Global.env() in
  List.iter
    (fun (gr,_,_) ->
       let typ = Global.type_of_global gr in
       if extra_filter gr env typ then
	 display_function gr env typ
    ) (search_function pat)

let text_pattern_search extra_filter pat =
  let ans = ref [] in
  raw_search Libtypes.search_concl extra_filter (plain_display ans) pat;
  format_display !ans

let text_search_rewrite extra_filter pat =
  let ans = ref [] in
  raw_search (Libtypes.search_eq_concl c_eq) extra_filter (plain_display ans) pat;
  format_display !ans

let text_search_by_head extra_filter pat =
  let ans = ref [] in
  raw_search Libtypes.search_head_concl extra_filter (plain_display ans) pat;
  format_display !ans

let filter_by_module_from_list = function
  | [], _ -> (fun _ _ _ -> true)
  | l, outside -> filter_by_module l (not outside)

let filter_blacklist gr _ _ =
  let name = full_name_of_reference gr in
  let l = SearchBlacklist.elements () in
  List.for_all (fun str -> not (String.string_contains ~where:name ~what:str)) l

let (&&&&&) f g x y z = f x y z && g x y z

let search_by_head pat inout =
  text_search_by_head (filter_by_module_from_list inout &&&&& filter_blacklist) pat

let search_rewrite pat inout =
  text_search_rewrite (filter_by_module_from_list inout &&&&& filter_blacklist) pat

let search_pattern pat inout =
  text_pattern_search (filter_by_module_from_list inout &&&&& filter_blacklist) pat

let gen_filtered_search filter_function display_function =
  gen_crible None
    (fun s a c -> if filter_function s a c then display_function s a c)

(** SearchAbout *)

type glob_search_about_item =
  | GlobSearchSubPattern of constr_pattern
  | GlobSearchString of string

let search_about_item (itemref,typ) = function
  | GlobSearchSubPattern pat -> is_matching_appsubterm ~closed:false pat typ
  | GlobSearchString s -> String.string_contains ~where:(name_of_reference itemref) ~what:s

let raw_search_about filter_modules display_function l =
  let filter ref' env typ =
    filter_modules ref' env typ &&
    List.for_all (fun (b,i) -> b = search_about_item (ref',typ) i) l &&
      filter_blacklist ref' () ()
  in
  gen_filtered_search filter display_function

let search_about reference inout =
  let ans = ref [] in
  raw_search_about (filter_by_module_from_list inout) (plain_display ans) reference;
  format_display !ans

let interface_search flags =
  let env = Global.env () in
  let rec extract_flags name tpe subtpe mods blacklist = function
  | [] -> (name, tpe, subtpe, mods, blacklist)
  | (Interface.Name_Pattern s, b) :: l ->
    let regexp =
      try Str.regexp s
      with _ -> Errors.error ("Invalid regexp: " ^ s)
    in
    extract_flags ((regexp, b) :: name) tpe subtpe mods blacklist l
  | (Interface.Type_Pattern s, b) :: l ->
    let constr = Pcoq.parse_string Pcoq.Constr.lconstr_pattern s in
    let (_, pat) = Constrintern.intern_constr_pattern Evd.empty env constr in
    extract_flags name ((pat, b) :: tpe) subtpe mods blacklist l
  | (Interface.SubType_Pattern s, b) :: l ->
    let constr = Pcoq.parse_string Pcoq.Constr.lconstr_pattern s in
    let (_, pat) = Constrintern.intern_constr_pattern Evd.empty env constr in
    extract_flags name tpe ((pat, b) :: subtpe) mods blacklist l
  | (Interface.In_Module m, b) :: l ->
    let path = String.concat "." m in
    let m = Pcoq.parse_string Pcoq.Constr.global path in
    let (_, qid) = Libnames.qualid_of_reference m in
    let id =
      try Nametab.full_name_module qid
      with Not_found ->
        Errors.error ("Module " ^ path ^ " not found.")
    in
    extract_flags name tpe subtpe ((id, b) :: mods) blacklist l
  | (Interface.Include_Blacklist, b) :: l ->
    extract_flags name tpe subtpe mods b l
  in
  let (name, tpe, subtpe, mods, blacklist) =
    extract_flags [] [] [] [] false flags
  in
  let filter_function ref env constr =
    let id = Names.string_of_id (Nametab.basename_of_global ref) in
    let path = Libnames.dirpath (Nametab.path_of_global ref) in
    let toggle x b = if x then b else not b in
    let match_name (regexp, flag) =
      toggle (Str.string_match regexp id 0) flag
    in
    let match_type (pat, flag) =
      toggle (Matching.is_matching pat constr) flag
    in
    let match_subtype (pat, flag) =
      toggle (Matching.is_matching_appsubterm ~closed:false pat constr) flag
    in
    let match_module (mdl, flag) =
      toggle (Libnames.is_dirpath_prefix_of mdl path) flag
    in
    let in_blacklist =
      blacklist || (filter_blacklist ref env constr)
    in
    List.for_all match_name name &&
    List.for_all match_type tpe &&
    List.for_all match_subtype subtpe &&
    List.for_all match_module mods && in_blacklist
  in
  let ans = ref [] in
  let print_function ref env constr =
    let fullpath = repr_dirpath (Nametab.dirpath_of_global ref) in
    let qualid = Nametab.shortest_qualid_of_global Idset.empty ref in
    let (shortpath, basename) = Libnames.repr_qualid qualid in
    let shortpath = repr_dirpath shortpath in
    (* [shortpath] is a suffix of [fullpath] and we're looking for the missing
       prefix *)
    let rec prefix full short accu = match full, short with
    | _, [] ->
      let full = List.rev_map string_of_id full in
      (full, accu)
    | _ :: full, m :: short ->
      prefix full short (string_of_id m :: accu)
    | _ -> assert false
    in
    let (prefix, qualid) = prefix fullpath shortpath [string_of_id basename] in
    let answer = {
      Interface.coq_object_prefix = prefix;
      Interface.coq_object_qualid = qualid;
      Interface.coq_object_object = string_of_ppcmds (pr_lconstr_env env constr);
    } in
    ans := answer :: !ans;
  in
  let () = gen_filtered_search filter_function print_function in
  !ans
