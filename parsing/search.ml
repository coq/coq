(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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
open Coqast
open Environ
open Pattern
open Printer
open Libnames
open Nametab

(* The functions print_constructors and crible implement the behavior needed
   for the Coq searching commands.
   These functions take as first argument the procedure
   that will be called to treat each entry.  This procedure receives the name
   of the object, the assumptions that will make it possible to print its type,
   and the constr term that represent its type. *)

let print_constructors indsp fn env mip =
  let lc = mip.mind_user_lc in
  for i = 1 to Array.length lc do
    fn (ConstructRef (indsp,i)) env
      (Retyping.get_type_of env Evd.empty
	 (Pretyping.understand Evd.empty env
	    (RRef(dummy_loc, ConstructRef(indsp,i)))))
  done

let rec head_const c = match kind_of_term c with
  | Prod (_,_,d) -> head_const d
  | LetIn (_,_,_,d) -> head_const d
  | App (f,_)   -> head_const f
  | Cast (d,_)   -> head_const d
  | _            -> c

let crible (fn : global_reference -> env -> constr -> unit) ref =
  let env = Global.env () in
  let imported = Library.opened_libraries() in
  let const = constr_of_reference ref in 
  let crible_rec (sp,_) lobj =
    match object_tag lobj with
      | "VARIABLE" ->
	  (try 
	     let (idc,_,typ) = get_variable (basename sp) in 
             if (head_const typ) = const then fn (VarRef idc) env typ
	   with Not_found -> (* we are in a section *) ())
      | "CONSTANT" ->
	  let kn = locate_constant (qualid_of_sp sp) in
	  let {const_type=typ} = Global.lookup_constant kn in
	  if (head_const typ) = const then fn (ConstRef kn) env typ
      | "INDUCTIVE" -> 
	  let kn = locate_mind (qualid_of_sp sp) in
          let mib = Global.lookup_mind kn in 
(*	  let arities =
	    array_map_to_list 
	      (fun mip ->
		 (Name mip.mind_typename, None, mip.mind_nf_arity))
	      mib.mind_packets in*)
          (match kind_of_term const with 
	     | Ind ((kn',tyi) as ind) -> 
		 if kn=kn' then
		   print_constructors ind fn env mib.mind_packets.(tyi)
	     | _ -> ())
      | _ -> ()
  in 
    try 
      Declaremods.iter_all_segments false crible_rec
    with Not_found -> 
      errorlabstrm "search"
      (pr_global ref ++ spc () ++ str "not declared")

(* Fine Search. By Yves Bertot. *)

exception No_section_path

let rec head c = 
  let c = strip_outer_cast c in
  match kind_of_term c with
  | Prod (_,_,c) -> head c
  | _              -> c
      
let constr_to_section_path c = match kind_of_term c with
  | Const sp -> sp
  | _ -> raise No_section_path
      
let xor a b = (a or b) & (not (a & b))

let plain_display ref a c =
  let pc = prterm_env a c in
  let pr = pr_global ref in
  msg (hov 2 (pr ++ str":" ++ spc () ++ pc) ++ fnl ())

let filter_by_module (module_list:dir_path list) (accept:bool) 
  (ref:global_reference) _ _ =
  try
    let sp = sp_of_global ref in
    let sl = dirpath sp in
    let rec filter_aux = function
      | m :: tl -> (not (is_dirpath_prefix_of m sl)) && (filter_aux tl)
      | [] -> true 
    in
    xor accept (filter_aux module_list)
  with No_section_path -> 
    false

let gref_eq =
  IndRef (Libnames.encode_kn Coqlib.logic_module (id_of_string "eq"), 0)
let gref_eqT =
  IndRef (Libnames.encode_kn Coqlib.logic_type_module (id_of_string "eqT"), 0)

let mk_rewrite_pattern1 eq pattern =
  PApp (PRef eq, [| PMeta None; pattern; PMeta None |])

let mk_rewrite_pattern2 eq pattern =
  PApp (PRef eq, [| PMeta None; PMeta None; pattern |])

let pattern_filter pat _ a c =
  try 
    try
      Pattern.is_matching pat (head c) 
    with _ -> 
      Pattern.is_matching
	pat (head (Typing.type_of (Global.env()) Evd.empty c))
    with UserError _ -> 
      false

let filtered_search filter_function display_function ref =
  crible 
    (fun s a c -> if filter_function s a c then display_function s a c) 
    ref

let rec id_from_pattern = function
  | PRef gr -> gr
(* should be appear as a PRef (VarRef sp) !!
  | PVar id -> Nametab.locate (make_qualid [] (string_of_id id))
 *)
  | PApp (p,_) -> id_from_pattern p
  | _ -> error "the pattern is not simple enough"
	
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
    display_function gref_eq;
  filtered_search
    (fun s a c ->
       ((pattern_filter (mk_rewrite_pattern1 gref_eqT pattern) s a c) ||
        (pattern_filter (mk_rewrite_pattern2 gref_eqT pattern) s a c)) 
       && extra_filter s a c)
    display_function gref_eqT

let text_pattern_search extra_filter =
  raw_pattern_search extra_filter plain_display
    
let text_search_rewrite extra_filter =
  raw_search_rewrite extra_filter plain_display

let filter_by_module_from_list = function
  | [], _ -> (fun _ _ _ -> true)
  | l, outside -> filter_by_module l (not outside)

let search_by_head ref inout = 
  filtered_search (filter_by_module_from_list inout) plain_display ref

let search_rewrite pat inout =
  text_search_rewrite (filter_by_module_from_list inout) pat

let search_pattern pat inout =
  text_pattern_search (filter_by_module_from_list inout) pat


(* General search, not restricted to head constant *)

let gen_crible (fn : global_reference -> env -> constr -> unit) =
  let env = Global.env () in
  let imported = Library.opened_libraries() in
  let crible_rec (sp,_) lobj = match object_tag lobj with
    | "VARIABLE" ->
	(try 
	   let (idc,_,typ) = get_variable (basename sp) in 
           fn (VarRef idc) env typ
	 with Not_found -> (* we are in a section *) ())
    | "CONSTANT" ->
	let kn = locate_constant (qualid_of_sp sp) in
	let {const_type=typ} = Global.lookup_constant kn in
	fn (ConstRef kn) env typ
    | "INDUCTIVE" -> 
	let kn = locate_mind (qualid_of_sp sp) in
        let mib = Global.lookup_mind kn in 
        Array.iteri 
	  (fun i -> print_constructors (kn,i) fn env) mib.mind_packets
    | _ -> ()
  in 
  try 
    Declaremods.iter_all_segments false crible_rec
  with Not_found -> 
    ()

let gen_filtered_search filter_function display_function =
  gen_crible 
    (fun s a c -> if filter_function s a c then display_function s a c) 

let raw_search_about filter_modules display_function ref =
  let c = constr_of_reference ref in
  let filter ref' env typ =
    filter_modules ref' env typ &&
    Termops.occur_term c typ
  in
  gen_filtered_search filter display_function

let search_about ref inout = 
  raw_search_about (filter_by_module_from_list inout) plain_display ref



