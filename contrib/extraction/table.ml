(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Names
open Term
open Declarations
open Nameops
open Summary
open Libobject
open Goptions
open Libnames
open Util
open Pp
open Miniml

(*S Utilities concerning [module_path] and [kernel_names] *)

let kn_of_r r = match r with 
    | ConstRef kn -> kn
    | IndRef (kn,_) -> kn
    | ConstructRef ((kn,_),_) -> kn
    | VarRef _ -> assert false

let current_toplevel () = fst (Lib.current_prefix ())

let rec base_mp = function 
  | MPdot (mp,l) -> base_mp mp 
  | mp -> mp 

let is_modfile = function 
  | MPfile _ -> true 
  | _ -> false

let is_toplevel mp = 
  mp = initial_path || mp = current_toplevel ()

let at_toplevel mp = 
  is_modfile mp || is_toplevel mp

let visible_kn kn = at_toplevel (base_mp (modpath kn))


(*S The main tables: constants, inductives, records, ... *)

(*s Constants tables. *) 

let terms = ref (KNmap.empty : ml_decl KNmap.t)
let init_terms () = terms := KNmap.empty
let add_term kn d = terms := KNmap.add kn d !terms
let lookup_term kn = KNmap.find kn !terms

let types = ref (KNmap.empty : ml_schema KNmap.t)
let init_types () = types := KNmap.empty
let add_type kn s = types := KNmap.add kn s !types
let lookup_type kn = KNmap.find kn !types 

(*s Inductives table. *)

let inductives = ref (KNmap.empty : ml_ind KNmap.t)
let init_inductives () = inductives := KNmap.empty
let add_ind kn m = inductives := KNmap.add kn m !inductives
let lookup_ind kn = KNmap.find kn !inductives

(*s Recursors table. *)

let recursors = ref KNset.empty
let init_recursors () = recursors := KNset.empty

let add_recursors env kn = 
  let make_kn id = make_kn (modpath kn) empty_dirpath (label_of_id id) in 
  let mib = Environ.lookup_mind kn env in 
  Array.iter 
    (fun mip -> 
       let id = mip.mind_typename in 
       let kn_rec = make_kn (Nameops.add_suffix id "_rec")
       and kn_rect = make_kn (Nameops.add_suffix id "_rect") in 
       recursors := KNset.add kn_rec (KNset.add kn_rect !recursors))
    mib.mind_packets

let is_recursor = function 
  | ConstRef kn -> KNset.mem kn !recursors
  | _ -> false

(*s Record tables. *)

let records = ref (KNmap.empty : global_reference list KNmap.t)
let init_records () = records := KNmap.empty

let projs = ref (Refmap.empty : int Refmap.t)
let init_projs () = projs := Refmap.empty

let add_record kn n (l1,l2) = 
  records := KNmap.add kn l1 !records; 
  projs := List.fold_right (fun r -> Refmap.add r n) l2 !projs

let find_projections kn = KNmap.find kn !records
let is_projection r = Refmap.mem r !projs
let projection_arity r = Refmap.find r !projs

(*s Tables synchronization. *)

let reset_tables () = 
  init_terms (); init_types (); init_inductives (); init_recursors (); 
  init_records (); init_projs ()

(*s Printing. *)

(* The following functions work even on objects not in [Global.env ()].
   WARNING: for inductive objects, an extract_inductive must have been 
   done before. *)

let id_of_global = function 
  | ConstRef kn -> let _,_,l = repr_kn kn in id_of_label l
  | IndRef (kn,i) -> (lookup_ind kn).ind_packets.(i).ip_typename
  | ConstructRef ((kn,i),j) -> (lookup_ind kn).ind_packets.(i).ip_consnames.(j-1)
  | _ -> assert false

let pr_global r = pr_id (id_of_global r)

(*S Warning and Error messages. *)

let err s = errorlabstrm "Extraction" s

let error_axiom_scheme r i = 
  err (str "The type scheme axiom " ++ spc () ++
       pr_global r ++ spc () ++ str "needs " ++ pr_int i ++ 
       str " type variable(s).") 

let warning_info_ax r =
  Options.if_verbose msg_warning
    (str "You must realize axiom " ++
     pr_global r ++ str " in the extracted code.")

let warning_log_ax r = 
  Options.if_verbose msg_warning
    (str "This extraction depends on logical axiom" ++ spc () ++ 
     pr_global r ++ str "." ++ spc() ++ 
     str "Having false logical axiom in the environment when extracting" ++ 
     spc () ++ str "may lead to incorrect or non-terminating ML terms.")

let check_inside_module () = 
  try 
    ignore (Lib.what_is_opened ()); 
    Options.if_verbose warning
      ("Extraction inside an opened module is experimental.\n"^
       "In case of problem, close it first.\n"); 
    Pp.flush_all ()
  with Not_found -> ()

let check_inside_section () = 
  if Lib.sections_are_opened () then 
    err (str "You can't do that within a section." ++ fnl () ++
	 str "Close it and try again.")

let error_constant r = 
  err (Printer.pr_global r ++ str " is not a constant.") 

let error_inductive r = 
  err (Printer.pr_global r ++ spc () ++ str "is not an inductive type.")

let error_nb_cons () = 
  err (str "Not the right number of constructors.")

let error_module_clash s = 
  err (str ("There are two Coq modules with ML name " ^ s ^".\n") ++ 
       str "This is not allowed in ML. Please do some renaming first.")

let error_unknown_module m = 
  err (str "Module" ++ spc () ++ pr_qualid m ++ spc () ++ str "not found.") 

let error_toplevel () = 
  err (str "Toplevel pseudo-ML language can be used only at Coq toplevel.\n" ++
       str "You should use Extraction Language Ocaml or Haskell before.") 

let error_scheme () = 
  err (str "No Scheme modular extraction available yet.")

let error_not_visible r = 
  err (Printer.pr_global r ++ str " is not directly visible.\n" ++
       str "For example, it may be inside an applied functor." ++
       str "Use Recursive Extraction to get the whole environment.")

let error_unqualified_name s1 s2 = 
  err (str (s1 ^ " is used in " ^ s2 ^ " where it cannot be disambiguated\n" ^
	    "in ML from another name sharing the same basename.\n"  ^
	    "Please do some renaming.\n"))

(*S The Extraction auxiliary commands *)

(*s Extraction AutoInline *)

let auto_inline_ref = ref true

let auto_inline () = !auto_inline_ref

let _ = declare_bool_option 
	  {optsync = true;
	   optname = "Extraction AutoInline";
	   optkey = SecondaryTable ("Extraction", "AutoInline");
	   optread = auto_inline; 
	   optwrite = (:=) auto_inline_ref}


(*s Extraction Optimize *)

let optim_ref = ref true

let optim () = !optim_ref 

let _ = declare_bool_option 
	  {optsync = true; 
	   optname = "Extraction Optimize";
	   optkey = SecondaryTable ("Extraction", "Optimize");
	   optread = optim; 
	   optwrite = (:=) optim_ref}


(*s Extraction Lang *)

type lang = Ocaml | Haskell | Scheme | Toplevel

let lang_ref = ref Ocaml

let lang () = !lang_ref

let (extr_lang,_) = 
  declare_object 
    {(default_object "Extraction Lang") with  
       cache_function = (fun (_,l) -> lang_ref := l);
       load_function = (fun _ (_,l) -> lang_ref := l);
       export_function = (fun x -> Some x)}

let _ = declare_summary "Extraction Lang" 
	  { freeze_function = (fun () -> !lang_ref);
	    unfreeze_function = ((:=) lang_ref);
	    init_function = (fun () -> lang_ref := Ocaml);
	    survive_module = false;
	    survive_section = true }  
	  
let extraction_language x = Lib.add_anonymous_leaf (extr_lang x)


(*s Extraction Inline/NoInline *)

let empty_inline_table = (Refset.empty,Refset.empty)

let inline_table = ref empty_inline_table

let to_inline r = Refset.mem r (fst !inline_table)

let to_keep r = Refset.mem r (snd !inline_table)

let add_inline_entries b l = 
  let f b = if b then Refset.add else Refset.remove in 
  let i,k = !inline_table in 
  inline_table := 
  (List.fold_right (f b) l i), 
  (List.fold_right (f (not b)) l k)

(* Registration of operations for rollback. *)

let (inline_extraction,_) = 
  declare_object 
    {(default_object "Extraction Inline") with 
       cache_function = (fun (_,(b,l)) -> add_inline_entries b l);
       load_function = (fun _ (_,(b,l)) -> add_inline_entries b l);
       export_function = (fun x -> Some x); 
       classify_function = (fun (_,o) -> Substitute o); 
       subst_function = (fun (_,s,(b,l)) -> (b,(List.map (subst_global s) l))) }

let _ = declare_summary "Extraction Inline"
	  { freeze_function = (fun () -> !inline_table);
	    unfreeze_function = ((:=) inline_table);
	    init_function = (fun () -> inline_table := empty_inline_table);
	    survive_module = false;
	    survive_section = true }

(* Grammar entries. *)

let extraction_inline b l =
  check_inside_section (); 
  check_inside_module ();
  let refs = List.map Nametab.global l in 
  List.iter 
    (fun r -> match r with 
       | ConstRef _ -> ()
       | _ -> error_constant r) refs; 
  Lib.add_anonymous_leaf (inline_extraction (b,refs))

(* Printing part *)

let print_extraction_inline () = 
  let (i,n)= !inline_table in 
  let i'= Refset.filter (function ConstRef _ -> true | _ -> false) i in 
  msg 
    (str "Extraction Inline:" ++ fnl () ++ 
     Refset.fold
       (fun r p -> 
	  (p ++ str "   " ++ Printer.pr_global r ++ fnl ())) i' (mt ()) ++
     str "Extraction NoInline:" ++ fnl () ++ 
     Refset.fold
       (fun r p -> 
	  (p ++ str "   " ++ Printer.pr_global r ++ fnl ())) n (mt ()))

(* Reset part *)

let (reset_inline,_) = 
  declare_object
    {(default_object "Reset Extraction Inline") with  
       cache_function = (fun (_,_)-> inline_table :=  empty_inline_table);
       load_function = (fun _ (_,_)-> inline_table :=  empty_inline_table); 
       export_function = (fun x -> Some x)}

let reset_extraction_inline () = Lib.add_anonymous_leaf (reset_inline ())


(*s Extract Constant/Inductive. *)

(* UGLY HACK: to be defined in [extraction.ml] *)
let use_type_scheme_nb_args, register_type_scheme_nb_args = 
  let r = ref (fun _ _ -> 0) in (fun x y -> !r x y), (:=) r 

let customs = ref Refmap.empty

let add_custom r ids s = customs := Refmap.add r (ids,s) !customs

let is_custom r = Refmap.mem r !customs

let is_inline_custom r = (is_custom r) && (to_inline r) 

let find_custom r = snd (Refmap.find r !customs)

let find_type_custom r = Refmap.find r !customs

(* Registration of operations for rollback. *)

let (in_customs,_) = 
  declare_object 
    {(default_object "ML extractions") with 
       cache_function = (fun (_,(r,ids,s)) -> add_custom r ids s);
       load_function = (fun _ (_,(r,ids,s)) -> add_custom r ids s);
       export_function = (fun x -> Some x)}

let _ = declare_summary "ML extractions"
	  { freeze_function = (fun () -> !customs);
	    unfreeze_function = ((:=) customs);
	    init_function = (fun () -> customs := Refmap.empty);
	    survive_module = false;
	    survive_section = true }

(* Grammar entries. *)

let extract_constant_inline inline r ids s =
  check_inside_section ();
  check_inside_module ();
  let g = Nametab.global r in 
  match g with 
    | ConstRef kn -> 
	let env = Global.env () in 
	let typ = Environ.constant_type env kn in 
	let typ = Reduction.whd_betadeltaiota env typ in
	if Reduction.is_arity env typ 
	  then begin 
	    let nargs = use_type_scheme_nb_args env typ in 
	    if List.length ids <> nargs then error_axiom_scheme g nargs
	  end; 
	Lib.add_anonymous_leaf (inline_extraction (inline,[g]));
	Lib.add_anonymous_leaf (in_customs (g,ids,s))
    | _ -> error_constant g


let extract_inductive r (s,l) =
  check_inside_section ();
  check_inside_module ();
  let g = Nametab.global r in 
  match g with
    | IndRef ((kn,i) as ip) ->
	let mib = Global.lookup_mind kn in
	let n = Array.length mib.mind_packets.(i).mind_consnames in
	if n <> List.length l then error_nb_cons (); 
	Lib.add_anonymous_leaf (inline_extraction (true,[g]));
	Lib.add_anonymous_leaf (in_customs (g,[],s));
	list_iter_i
	  (fun j s -> 
	     let g = ConstructRef (ip,succ j) in 
	     Lib.add_anonymous_leaf (inline_extraction (true,[g]));
	     Lib.add_anonymous_leaf (in_customs (g,[],s))) l
    | _ -> error_inductive g 


