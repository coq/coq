(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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

(*S Utilities about [module_path] and [kernel_names] and [global_reference] *)

let occur_kn_in_ref kn = function
  | IndRef (kn',_)
  | ConstructRef ((kn',_),_) -> kn = kn'
  | ConstRef _ -> false
  | VarRef _ -> assert false

let modpath_of_r = function
  | ConstRef kn -> con_modpath kn
  | IndRef (kn,_)
  | ConstructRef ((kn,_),_) -> modpath kn
  | VarRef _ -> assert false

let label_of_r = function
  | ConstRef kn -> con_label kn
  | IndRef (kn,_)
  | ConstructRef ((kn,_),_) -> label kn
  | VarRef _ -> assert false

let rec base_mp = function
  | MPdot (mp,l) -> base_mp mp
  | mp -> mp

let rec mp_length = function
  | MPdot (mp, _) -> 1 + (mp_length mp)
  | _ -> 1

let is_modfile = function
  | MPfile _ -> true
  | _ -> false

let string_of_modfile = function
  | MPfile f -> String.capitalize (string_of_id (List.hd (repr_dirpath f)))
  | _ -> assert false

let rec modfile_of_mp = function
  | (MPfile _) as mp -> mp
  | MPdot (mp,_) -> modfile_of_mp mp
  | _ -> raise Not_found

let current_toplevel () = fst (Lib.current_prefix ())

let is_toplevel mp =
  mp = initial_path || mp = current_toplevel ()

let at_toplevel mp =
  is_modfile mp || is_toplevel mp

let visible_kn kn = at_toplevel (base_mp (modpath kn))
let visible_con kn = at_toplevel (base_mp (con_modpath kn))

let rec prefixes_mp mp = match mp with
  | MPdot (mp',_) -> MPset.add mp (prefixes_mp mp')
  | _ -> MPset.singleton mp

let rec get_nth_label_mp n = function
  | MPdot (mp,l) -> if n=1 then l else get_nth_label_mp (n-1) mp
  | _ -> failwith "get_nth_label: not enough MPdot"

let common_prefix_from_list mp0 mpl =
  let prefixes = prefixes_mp mp0 in
  let rec f = function
    | [] -> raise Not_found
    | mp :: l -> if MPset.mem mp prefixes then mp else f l
  in f mpl

let rec parse_labels ll = function
  | MPdot (mp,l) -> parse_labels (l::ll) mp
  | mp -> mp,ll

let labels_of_mp mp = parse_labels [] mp

let labels_of_ref r =
 let mp,_,l =
  match r with
     ConstRef con -> repr_con con
   | IndRef (kn,_)
   | ConstructRef ((kn,_),_) -> repr_kn kn
   | VarRef _ -> assert false
 in
  parse_labels [l] mp

let rec add_labels_mp mp = function
  | [] -> mp
  | l :: ll -> add_labels_mp (MPdot (mp,l)) ll


(*S The main tables: constants, inductives, records, ... *)

(* Theses tables are not registered within coq save/undo mechanism
   since we reset their contents at each run of Extraction *)

(*s Constants tables. *)

let terms = ref (Cmap.empty : ml_decl Cmap.t)
let init_terms () = terms := Cmap.empty
let add_term kn d = terms := Cmap.add kn d !terms
let lookup_term kn = Cmap.find kn !terms

let types = ref (Cmap.empty : ml_schema Cmap.t)
let init_types () = types := Cmap.empty
let add_type kn s = types := Cmap.add kn s !types
let lookup_type kn = Cmap.find kn !types

(*s Inductives table. *)

let inductives = ref (KNmap.empty : (mutual_inductive_body * ml_ind) KNmap.t)
let init_inductives () = inductives := KNmap.empty
let add_ind kn mib ml_ind = inductives := KNmap.add kn (mib,ml_ind) !inductives
let lookup_ind kn = KNmap.find kn !inductives

(*s Recursors table. *)

let recursors = ref Cset.empty
let init_recursors () = recursors := Cset.empty

let add_recursors env kn =
  let make_kn id = make_con (modpath kn) empty_dirpath (label_of_id id) in
  let mib = Environ.lookup_mind kn env in
  Array.iter
    (fun mip ->
       let id = mip.mind_typename in
       let kn_rec = make_kn (Nameops.add_suffix id "_rec")
       and kn_rect = make_kn (Nameops.add_suffix id "_rect") in
       recursors := Cset.add kn_rec (Cset.add kn_rect !recursors))
    mib.mind_packets

let is_recursor = function
  | ConstRef kn -> Cset.mem kn !recursors
  | _ -> false

(*s Record tables. *)

let projs = ref (Refmap.empty : int Refmap.t)
let init_projs () = projs := Refmap.empty
let add_projection n kn = projs := Refmap.add (ConstRef kn) n !projs
let is_projection r = Refmap.mem r !projs
let projection_arity r = Refmap.find r !projs

(*s Table of used axioms *)

let info_axioms = ref Refset.empty
let log_axioms = ref Refset.empty
let init_axioms () = info_axioms := Refset.empty; log_axioms := Refset.empty
let add_info_axiom r = info_axioms := Refset.add r !info_axioms
let remove_info_axiom r = info_axioms := Refset.remove r !info_axioms
let add_log_axiom r = log_axioms := Refset.add r !log_axioms

(*s Extraction mode: modular or monolithic *)

let modular_ref = ref false

let set_modular b = modular_ref := b
let modular () = !modular_ref

(*s Tables synchronization. *)

let reset_tables () =
  init_terms (); init_types (); init_inductives (); init_recursors ();
  init_projs (); init_axioms ()

(*s Printing. *)

(* The following functions work even on objects not in [Global.env ()].
   WARNING: for inductive objects, an extract_inductive must have been
   done before. *)

let safe_id_of_global = function
  | ConstRef kn -> let _,_,l = repr_con kn in id_of_label l
  | IndRef (kn,i) -> (snd (lookup_ind kn)).ind_packets.(i).ip_typename
  | ConstructRef ((kn,i),j) ->
      (snd (lookup_ind kn)).ind_packets.(i).ip_consnames.(j-1)
  | _ -> assert false

let safe_pr_global r =
 try Printer.pr_global r
 with _ -> pr_id (safe_id_of_global r)

(* idem, but with qualification, and only for constants. *)

let safe_pr_long_global r =
  try Printer.pr_global r
  with _ -> match r with
    | ConstRef kn ->
	let mp,_,l = repr_con kn in
	str ((string_of_mp mp)^"."^(string_of_label l))
    | _ -> assert false

let pr_long_mp mp =
  let lid = repr_dirpath (Nametab.dir_of_mp mp) in
  str (String.concat "." (List.map string_of_id (List.rev lid)))

let pr_long_global ref = pr_sp (Nametab.sp_of_global ref)

(*S Warning and Error messages. *)

let err s = errorlabstrm "Extraction" s

let warning_axioms () =
  let info_axioms = Refset.elements !info_axioms in
  if info_axioms = [] then ()
  else begin
    let s = if List.length info_axioms = 1 then "axiom" else "axioms" in
    msg_warning
      (str ("The following "^s^" must be realized in the extracted code:")
       ++ hov 1 (spc () ++ prlist_with_sep spc safe_pr_global info_axioms)
       ++ str "." ++ fnl ())
  end;
  let log_axioms = Refset.elements !log_axioms in
  if log_axioms = [] then ()
  else begin
    let s = if List.length log_axioms = 1 then "axiom was" else "axioms were"
    in
    msg_warning
      (str ("The following logical "^s^" encountered:") ++
       hov 1
         (spc () ++ prlist_with_sep spc safe_pr_global log_axioms ++ str ".\n")
       ++
       str "Having invalid logical axiom in the environment when extracting" ++
       spc () ++ str "may lead to incorrect or non-terminating ML terms." ++
       fnl ())
  end

let warning_both_mod_and_cst q mp r =
 msg_warning
   (str "The name " ++ pr_qualid q ++ str " is ambiguous, " ++
    str "do you mean module " ++
    pr_long_mp mp ++
    str " or object " ++
    pr_long_global r ++ str " ?" ++ fnl () ++
    str "First choice is assumed, for the second one please use " ++
    str "fully qualified name." ++ fnl ())

let error_axiom_scheme r i =
  err (str "The type scheme axiom " ++ spc () ++
       safe_pr_global r ++ spc () ++ str "needs " ++ pr_int i ++
       str " type variable(s).")

let check_inside_module () =
  if Lib.is_modtype () then
    err (str "You can't do that within a Module Type." ++ fnl () ++
	 str "Close it and try again.")
  else if Lib.is_module () then
    msg_warning
      (str "Extraction inside an opened module is experimental.\n" ++
       str "In case of problem, close it first.\n")

let check_inside_section () =
  if Lib.sections_are_opened () then
    err (str "You can't do that within a section." ++ fnl () ++
	 str "Close it and try again.")

let error_constant r =
  err (safe_pr_global r ++ str " is not a constant.")

let error_inductive r =
  err (safe_pr_global r ++ spc () ++ str "is not an inductive type.")

let error_nb_cons () =
  err (str "Not the right number of constructors.")

let error_module_clash s =
  err (str ("There are two Coq modules with ML name " ^ s ^".\n") ++
       str "This is not supported yet. Please do some renaming first.")

let error_unknown_module m =
  err (str "Module" ++ spc () ++ pr_qualid m ++ spc () ++ str "not found.")

let error_scheme () =
  err (str "No Scheme modular extraction available yet.")

let error_not_visible r =
  err (safe_pr_global r ++ str " is not directly visible.\n" ++
       str "For example, it may be inside an applied functor." ++
       str "Use Recursive Extraction to get the whole environment.")

let error_MPfile_as_mod mp b =
  let s1 = if b then "asked" else "required" in
  let s2 = if b then "extract some objects of this module or\n" else "" in
  err (str ("Extraction of file "^(string_of_modfile mp)^
	    ".v as a module is "^s1^".\n"^
	    "Monolithic Extraction cannot deal with this situation.\n"^
	    "Please "^s2^"use (Recursive) Extraction Library instead.\n"))

let error_record r =
  err (str "Record " ++ safe_pr_global r ++ str " has an anonymous field." ++
       fnl () ++ str "To help extraction, please use an explicit name.")

let check_loaded_modfile mp = match base_mp mp with
  | MPfile dp -> if not (Library.library_is_loaded dp) then
      err (str ("Please load library "^(string_of_dirpath dp^" first.")))
  | _ -> ()

let info_file f =
  Flags.if_verbose message
    ("The file "^f^" has been created by extraction.")


(*S The Extraction auxiliary commands *)

(* The objects defined below should survive an arbitrary time,
   so we register them to coq save/undo mechanism. *)

(*s Extraction AutoInline *)

let auto_inline_ref = ref true

let auto_inline () = !auto_inline_ref

let _ = declare_bool_option
	  {optsync = true;
	   optname = "Extraction AutoInline";
	   optkey = SecondaryTable ("Extraction", "AutoInline");
	   optread = auto_inline;
	   optwrite = (:=) auto_inline_ref}

(*s Extraction TypeExpand *)

let type_expand_ref = ref true

let type_expand () = !type_expand_ref

let _ = declare_bool_option
	  {optsync = true;
	   optname = "Extraction TypeExpand";
	   optkey = SecondaryTable ("Extraction", "TypeExpand");
	   optread = type_expand;
	   optwrite = (:=) type_expand_ref}

(*s Extraction Optimize *)

type opt_flag =
    { opt_kill_dum : bool; (* 1 *)
      opt_fix_fun : bool;   (* 2 *)
      opt_case_iot : bool;  (* 4 *)
      opt_case_idr : bool;  (* 8 *)
      opt_case_idg : bool;  (* 16 *)
      opt_case_cst : bool;  (* 32 *)
      opt_case_fun : bool;  (* 64 *)
      opt_case_app : bool;  (* 128 *)
      opt_let_app : bool;   (* 256 *)
      opt_lin_let : bool;   (* 512 *)
      opt_lin_beta : bool } (* 1024 *)

let kth_digit n k = (n land (1 lsl k) <> 0)

let flag_of_int n =
    { opt_kill_dum = kth_digit n 0;
      opt_fix_fun = kth_digit n 1;
      opt_case_iot = kth_digit n 2;
      opt_case_idr = kth_digit n 3;
      opt_case_idg = kth_digit n 4;
      opt_case_cst = kth_digit n 5;
      opt_case_fun = kth_digit n 6;
      opt_case_app = kth_digit n 7;
      opt_let_app = kth_digit n 8;
      opt_lin_let = kth_digit n 9;
      opt_lin_beta = kth_digit n 10 }

(* For the moment, we allow by default everything except the type-unsafe
   optimization [opt_case_idg]. *)

let int_flag_init = 1 + 2 + 4 + 8 + 32 + 64 + 128 + 256 + 512 + 1024

let int_flag_ref = ref int_flag_init
let opt_flag_ref = ref (flag_of_int int_flag_init)

let chg_flag n = int_flag_ref := n; opt_flag_ref := flag_of_int n

let optims () = !opt_flag_ref

let _ = declare_bool_option
	  {optsync = true;
	   optname = "Extraction Optimize";
	   optkey = SecondaryTable ("Extraction", "Optimize");
	   optread = (fun () -> !int_flag_ref <> 0);
	   optwrite = (fun b -> chg_flag (if b then int_flag_init else 0))}

let _ = declare_int_option
          { optsync = true;
            optname = "Extraction Flag";
            optkey = SecondaryTable("Extraction","Flag");
            optread = (fun _ -> Some !int_flag_ref);
            optwrite = (function
                          | None -> chg_flag 0
                          | Some i -> chg_flag (max i 0))}


(*s Extraction Lang *)

type lang = Ocaml | Haskell | Scheme

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
	    survive_module = true;
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
       subst_function =
        (fun (_,s,(b,l)) -> (b,(List.map (fun x -> fst (subst_global s x)) l)))
    }

let _ = declare_summary "Extraction Inline"
	  { freeze_function = (fun () -> !inline_table);
	    unfreeze_function = ((:=) inline_table);
	    init_function = (fun () -> inline_table := empty_inline_table);
	    survive_module = true;
	    survive_section = true }

(* Grammar entries. *)

let extraction_inline b l =
  check_inside_section ();
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
	  (p ++ str "  " ++ safe_pr_long_global r ++ fnl ())) i' (mt ()) ++
     str "Extraction NoInline:" ++ fnl () ++
     Refset.fold
       (fun r p ->
	  (p ++ str "  " ++ safe_pr_long_global r ++ fnl ())) n (mt ()))

(* Reset part *)

let (reset_inline,_) =
  declare_object
    {(default_object "Reset Extraction Inline") with
       cache_function = (fun (_,_)-> inline_table :=  empty_inline_table);
       load_function = (fun _ (_,_)-> inline_table :=  empty_inline_table);
       export_function = (fun x -> Some x)}

let reset_extraction_inline () = Lib.add_anonymous_leaf (reset_inline ())

(*s Extraction Blacklist of filenames not to use while extracting *)

let blacklist_table = ref Stringset.empty

let is_blacklisted s =
 (Stringset.mem (String.capitalize s) !blacklist_table) ||
 (Stringset.mem (String.uncapitalize s) !blacklist_table)

let string_of_modfile mp =
  let s = string_of_modfile mp in
  if is_blacklisted s then "Coq_"^s else s

let add_blacklist_entries l =
  blacklist_table := List.fold_right Stringset.add l !blacklist_table

(* Registration of operations for rollback. *)

let (blacklist_extraction,_) =
  declare_object
    {(default_object "Extraction Blacklist") with
       cache_function = (fun (_,l) -> add_blacklist_entries l);
       load_function = (fun _ (_,l) -> add_blacklist_entries l);
       export_function = (fun x -> Some x);
       classify_function = (fun (_,o) -> Libobject.Keep o);
       subst_function = (fun (_,_,x) -> x)
    }

let _ = declare_summary "Extraction Blacklist"
	  { freeze_function = (fun () -> !blacklist_table);
	    unfreeze_function = ((:=) blacklist_table);
	    init_function = (fun () -> blacklist_table := Stringset.empty);
	    survive_module = true;
	    survive_section = true }

(* Grammar entries. *)

let extraction_blacklist l =
  let l = List.rev_map string_of_id l in
  Lib.add_anonymous_leaf (blacklist_extraction l)

(* Printing part *)

let print_extraction_blacklist () =
  msgnl
    (prlist_with_sep fnl str (Stringset.elements !blacklist_table))

(* Reset part *)

let (reset_blacklist,_) =
  declare_object
    {(default_object "Reset Extraction Blacklist") with
       cache_function = (fun (_,_)-> blacklist_table := Stringset.empty);
       load_function = (fun _ (_,_)-> blacklist_table := Stringset.empty);
       export_function = (fun x -> Some x)}

let reset_extraction_blacklist () = Lib.add_anonymous_leaf (reset_blacklist ())

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
       export_function = (fun x -> Some x);
       classify_function = (fun (_,o) -> Substitute o);
       subst_function =
        (fun (_,s,(r,ids,str)) -> (fst (subst_global s r), ids, str))
    }

let _ = declare_summary "ML extractions"
	  { freeze_function = (fun () -> !customs);
	    unfreeze_function = ((:=) customs);
	    init_function = (fun () -> customs := Refmap.empty);
	    survive_module = true;
	    survive_section = true }

(* Grammar entries. *)

let extract_constant_inline inline r ids s =
  check_inside_section ();
  let g = Nametab.global r in
  match g with
    | ConstRef kn ->
	let env = Global.env () in
	let typ = Typeops.type_of_constant env kn in
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


