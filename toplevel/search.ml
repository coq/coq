(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Nameops
open Term
open Rawterm
open Declarations
open Libobject
open Declare
open Environ
open Pattern
open Matching
open Printer
open Libnames
open Nametab

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
	let cst = Global.constant_of_delta(constant_of_kn kn) in
	let typ = Typeops.type_of_constant env cst in
        if refopt = None
	  || head_const typ = constr_of_global (Option.get refopt)
	then
	  fn (ConstRef cst) env typ
    | "INDUCTIVE" ->
	let mind = Global.mind_of_delta(mind_of_kn kn) in
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

exception No_full_path

let rec head c =
  let c = strip_outer_cast c in
  match kind_of_term c with
  | Prod (_,_,c) -> head c
  | LetIn (_,_,_,c) -> head c
  | _              -> c

let constr_to_full_path c = match kind_of_term c with
  | Const sp -> sp
  | _ -> raise No_full_path

let xor a b = (a or b) & (not (a & b))

let plain_display ref a c =
  let pc = pr_lconstr_env a c in
  let pr = pr_global ref in
  msg (hov 2 (pr ++ str":" ++ spc () ++ pc) ++ fnl ())

let filter_by_module (module_list:dir_path list) (accept:bool)
  (ref:global_reference) _ _ =
  try
    let sp = path_of_global ref in
    let sl = dirpath sp in
    let rec filter_aux = function
      | m :: tl -> (not (is_dirpath_prefix_of m sl)) && (filter_aux tl)
      | [] -> true
    in
    xor accept (filter_aux module_list)
  with No_full_path ->
    false

let ref_eq = Libnames.encode_mind Coqlib.logic_module (id_of_string "eq"), 0
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
  Util.todo "raw_search_by_head"

let name_of_reference ref = string_of_id (basename_of_global ref)

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

let text_pattern_search extra_filter =
  raw_search Libtypes.search_concl extra_filter plain_display

let text_search_rewrite extra_filter =
  raw_search (Libtypes.search_eq_concl c_eq) extra_filter plain_display

let text_search_by_head extra_filter =
  raw_search Libtypes.search_head_concl extra_filter plain_display

let filter_by_module_from_list = function
  | [], _ -> (fun _ _ _ -> true)
  | l, outside -> filter_by_module l (not outside)

let filter_subproof gr _ _ =
  not (string_string_contains (name_of_reference gr) "_subproof") &&
  not (string_string_contains (name_of_reference gr) "_admitted")

let (&&&&&) f g x y z = f x y z && g x y z

let search_by_head pat inout =
  text_search_by_head (filter_by_module_from_list inout &&&&& filter_subproof) pat

let search_rewrite pat inout =
  text_search_rewrite (filter_by_module_from_list inout &&&&& filter_subproof) pat

let search_pattern pat inout =
  text_pattern_search (filter_by_module_from_list inout &&&&& filter_subproof) pat

let gen_filtered_search filter_function display_function =
  gen_crible None
    (fun s a c -> if filter_function s a c then display_function s a c)

(** SearchAbout *)

type glob_search_about_item =
  | GlobSearchSubPattern of constr_pattern
  | GlobSearchString of string

let search_about_item (itemref,typ) = function
  | GlobSearchSubPattern pat -> is_matching_appsubterm ~closed:false pat typ
  | GlobSearchString s -> string_string_contains (name_of_reference itemref) s

let raw_search_about filter_modules display_function l =
  let filter ref' env typ =
    filter_modules ref' env typ &&
    List.for_all (fun (b,i) -> b = search_about_item (ref',typ) i) l &&
      filter_subproof ref' () ()
  in
  gen_filtered_search filter display_function

let search_about ref inout =
  raw_search_about (filter_by_module_from_list inout) plain_display ref
