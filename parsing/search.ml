
(* $Id$ *)

open Pp
open Util
open Names
open Term
open Declarations
open Libobject
open Declare
open Coqast
open Astterm
open Pretty
open Environ
open Pattern
open Printer

(* The functions print_constructors and crible implement the behavior needed
   for the Coq Search command.
   These functions take as first argument the procedure
   that will be called to treat each entry.  This procedure receives the name
   of the object, the assumptions that will make it possible to print its type,
   and the constr term that represent its type. *)

let print_constructors fn env_ar mip = 
  let _ =
    array_map2 (fun id c -> fn (pr_id id) (* il faudrait qualifier... *)
		    env_ar (body_of_type c))
    mip.mind_consnames (mind_user_lc mip)
  in ()

let rec head_const c = match kind_of_term c with
  | IsProd (_,_,d) -> head_const d
  | IsLetIn (_,_,_,d) -> head_const d
  | IsApp (f,_)   -> head_const f
  | IsCast (d,_)   -> head_const d
  | _            -> c

let crible (fn : std_ppcmds -> env -> constr -> unit) ref =
  let env = Global.env () in
  let imported = Library.opened_modules() in
  let const = constr_of_reference Evd.empty env ref in 
  let crible_rec sp lobj =
    match object_tag lobj with
      | "VARIABLE" ->
	  let ((idc,_,typ),_,_) = get_variable sp in 
          if (head_const (body_of_type typ)) = const then  
            fn (pr_id idc) env (body_of_type typ)
      | "CONSTANT" 
      | "PARAMETER" ->
	  let {const_type=typ} = Global.lookup_constant sp in
	  if (head_const (body_of_type typ)) = const then
            fn (pr_global (ConstRef sp)) env (body_of_type typ)
      | "INDUCTIVE" -> 
          let mib = Global.lookup_mind sp in 
	  let arities =
	    array_map_to_list 
	      (fun mip ->
		 (Name mip.mind_typename, None, mip.mind_nf_arity))
	      mib.mind_packets in
	  let env_ar = push_rels arities env in
          (match kind_of_term const with 
	     | IsMutInd ((sp',tyi),_) -> 
		 if sp=sp' then (*Suffit pas, cf les inds de Ensemble.v*)
		   print_constructors fn env_ar
		     (mind_nth_type_packet mib tyi)
	     | _ -> ())
      | _ -> ()
  in 
  try 
    Library.iter_all_segments false crible_rec 
  with Not_found -> 
    errorlabstrm "search"
      [< pr_global ref; 'sPC; 'sTR "not declared" >]

let search_by_head ref =
  crible (fun pname ass_name constr -> 
            let pc = prterm_env ass_name constr in
            mSG[< pname; 'sTR":"; pc; 'fNL >]) ref

(* Fine Search. By Yves Bertot. *)

exception No_section_path

let rec head c = 
  let c = strip_outer_cast c in
  match kind_of_term c with
  | IsProd (_,_,c) -> head c
  | _              -> c
      
let constr_to_section_path c = match kind_of_term c with
  | IsConst (sp,_) -> sp
  | _ -> raise No_section_path
      
let xor a b = (a or b) & (not (a & b))

let plain_display s a c =
  let pc = Printer.prterm_env a c in
  mSG [< s; 'sTR":"; pc; 'fNL>]

let filter_by_module module_list accept _ _ c =
  try
    let sp = constr_to_section_path c in
    let sl = dirpath sp in
    let rec filter_aux = function
      | m :: tl -> (not (List.mem m sl)) && (filter_aux tl)
      | [] -> true 
    in
    xor accept (filter_aux module_list)
  with No_section_path -> 
    false

let gref_eq = IndRef (make_path ["Coq";"Init";"Logic"] (id_of_string "eq") CCI, 0)
let gref_eqT = IndRef (make_path ["Coq";"Init";"Logic_Type"] (id_of_string "eqT") CCI, 0)

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
  | PVar id -> Nametab.sp_of_id CCI id
  | PApp (p,_) -> id_from_pattern p
  | _ -> error "the pattern is not simple enough"
	
let pattern_search extra_filter display_function pat =
  let name = id_from_pattern pat in
  filtered_search 
    (fun s a c -> (pattern_filter pat s a c) & extra_filter s a c) 
    display_function name

let search_rewrite extra_filter display_function pattern =
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
  pattern_search extra_filter plain_display
    
let text_search_rewrite extra_filter =
  search_rewrite extra_filter plain_display

let filter_by_module_from_list = function
  | [], _ -> (fun _ _ _ -> true)
  | l, s -> filter_by_module l (s = "inside")

let search_modules ref inout = 
  filtered_search (filter_by_module_from_list inout) plain_display ref

let search_rewrite pat inout =
  text_search_rewrite (filter_by_module_from_list inout) pat

let search_pattern pat inout =
  text_pattern_search (filter_by_module_from_list inout) pat


