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
open Summary
open Libobject
open Goptions
open Libnames
open Util
open Pp
open Miniml

(*S Warning and Error messages. *)

let error_axiom_scheme r = 
  errorlabstrm "Extraction" 
    (str "Extraction cannot accept the type scheme axiom " ++ spc () ++
     Printer.pr_global r ++ spc () ++ str ".") 

let error_axiom r =
  errorlabstrm "Extraction"
    (str "You must specify an extraction for axiom" ++ spc () ++ 
     Printer.pr_global r ++ spc () ++ str "first.")

let warning_axiom r = 
  Options.if_verbose warn 
    (str "This extraction depends on logical axiom" ++ spc () ++ 
     Printer.pr_global r ++ str "." ++ spc() ++ 
     str "Having false logical axiom in the environment when extracting" ++ 
     spc () ++ str "may lead to incorrect or non-terminating ML terms.")
    
let error_section () = 
  errorlabstrm "Extraction"
    (str "You can't do that within a section. Close it and try again.")

let error_constant r = 
  errorlabstrm "Extraction"
    (Printer.pr_global r ++ spc () ++ str "is not a constant.") 

let error_type_scheme r = 
  errorlabstrm "Extraction"
    (Printer.pr_global r ++ spc () ++ str "is a type scheme, not a type.")

let error_inductive r = 
  errorlabstrm "Extraction"
    (Printer.pr_global r ++ spc () ++ str "is not an inductive type.")

let error_nb_cons () = 
  errorlabstrm "Extraction" (str "Not the right number of constructors.")


(*S Extraction AutoInline *)

let auto_inline_ref = ref true

let auto_inline () = !auto_inline_ref

let _ = declare_bool_option 
	  {optsync = true;
	   optname = "Extraction AutoInline";
	   optkey = SecondaryTable ("Extraction", "AutoInline");
	   optread = auto_inline; 
	   optwrite = (:=) auto_inline_ref}


(*S Extraction Optimize *)

let optim_ref = ref true

let optim () = !optim_ref 

let _ = declare_bool_option 
	  {optsync = true; 
	   optname = "Extraction Optimize";
	   optkey = SecondaryTable ("Extraction", "Optimize");
	   optread = optim; 
	   optwrite = (:=) optim_ref}


(*S Extraction Lang *)

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
	    survive_section = true }  

let extraction_language x = Lib.add_anonymous_leaf (extr_lang x)


(*S Extraction Inline/NoInline *)

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

(*s Registration of operations for rollback. *)

let (inline_extraction,_) = 
  declare_object 
    {(default_object "Extraction Inline") with 
       cache_function = (fun (_,(b,l)) -> add_inline_entries b l);
       load_function = (fun _ (_,(b,l)) -> add_inline_entries b l);
       export_function = (fun x -> Some x)}

let _ = declare_summary "Extraction Inline"
	  { freeze_function = (fun () -> !inline_table);
	    unfreeze_function = ((:=) inline_table);
	    init_function = (fun () -> inline_table := empty_inline_table);
	    survive_section = true }

(*s Grammar entries. *)

let extraction_inline b l =
  if Lib.sections_are_opened () then error_section (); 
  let refs = List.map Nametab.global l in 
  List.iter (function  ConstRef _ -> () | r -> error_constant r) refs; 
  Lib.add_anonymous_leaf (inline_extraction (b,refs))

(*s Printing part *)

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

(*s Reset part *)

let (reset_inline,_) = 
  declare_object
    {(default_object "Reset Extraction Inline") with  
       cache_function = (fun (_,_)-> inline_table :=  empty_inline_table);
       load_function = (fun _ (_,_)-> inline_table :=  empty_inline_table); 
       export_function = (fun x -> Some x)}

let reset_extraction_inline () = Lib.add_anonymous_leaf (reset_inline ())


(*S Extract Constant/Inductive. *)

type kind = Term | Type | Ind | Construct 

let check_term_or_type r = match r with 
  | ConstRef sp -> 
      let env = Global.env () in 
      let typ = Environ.constant_type env sp in 
      let typ = Reduction.whd_betadeltaiota env typ in
      if isSort typ then (r,Type) 
      else if Reduction.is_arity env typ then error_type_scheme r
      else (r,Term)
  | _ -> error_constant r
	
let empty_extractions = (Refmap.empty, Refset.empty)

let extractions = ref empty_extractions

let ml_extractions () = snd !extractions

let ml_term_extractions () = 
  Refmap.fold (fun r (k,s) l -> if k=Term then (r,s)::l else l)
    (fst !extractions) []

let ml_type_extractions () = 
  Refmap.fold (fun r (k,s) l -> if k=Type then (r,s)::l else l) 
    (fst !extractions) []
    
let add_ml_extraction r k s = 
  let (map,set) = !extractions in
  extractions := (Refmap.add r (k,s) map, Refset.add r set)

let is_ml_extraction r = Refset.mem r (snd !extractions)

let find_ml_extraction r = snd (Refmap.find r (fst !extractions))

(*s Registration of operations for rollback. *)

let (in_ml_extraction,_) = 
  declare_object 
    {(default_object "ML extractions") with 
       cache_function = (fun (_,(r,k,s)) -> add_ml_extraction r k s);
       load_function = (fun _ (_,(r,k,s)) -> add_ml_extraction r k s);
       export_function = (fun x -> Some x)}

let _ = declare_summary "ML extractions"
	  { freeze_function = (fun () -> !extractions);
	    unfreeze_function = ((:=) extractions);
	    init_function = (fun () -> extractions := empty_extractions);
	    survive_section = true }

(*s Grammar entries. *)

let extract_constant_inline inline r s =
  if Lib.sections_are_opened () then error_section (); 
  let g,k = check_term_or_type (Nametab.global r) in
  Lib.add_anonymous_leaf (inline_extraction (inline,[g]));
  Lib.add_anonymous_leaf (in_ml_extraction (g,k,s))

let extract_inductive r (s,l) =
  if Lib.sections_are_opened () then error_section (); 
  let g = Nametab.global r in match g with
  | IndRef ((kn,i) as ip) ->
      let mib = Global.lookup_mind kn in
      let n = Array.length mib.mind_packets.(i).mind_consnames in
      if n <> List.length l then error_nb_cons (); 
      Lib.add_anonymous_leaf (inline_extraction (true,[g]));
      Lib.add_anonymous_leaf (in_ml_extraction (g,Ind,s));
      list_iter_i
	(fun j s -> 
	   let g = ConstructRef (ip,succ j) in 
	   Lib.add_anonymous_leaf (inline_extraction (true,[g]));
	   Lib.add_anonymous_leaf (in_ml_extraction (g,Construct,s))) l
  | _ -> error_inductive g 


(*S The other tables: constants, inductives, records, ... *)

(*s Constants tables. *) 

let terms = ref (KNmap.empty : ml_decl KNmap.t)
let add_term kn d = terms := KNmap.add kn d !terms
let lookup_term kn = KNmap.find kn !terms

let types = ref (KNmap.empty : ml_schema KNmap.t)
let add_type kn s = types := KNmap.add kn s !types
let lookup_type kn = KNmap.find kn !types 

(*s Inductives table. *)

let inductives = ref (KNmap.empty : ml_ind KNmap.t)
let add_ind kn m = inductives := KNmap.add kn m !inductives
let lookup_ind kn = KNmap.find kn !inductives

(*s Recursors table. *)

let recursors = ref KNset.empty

let add_recursors kn = 
  let make_kn id = make_kn (modpath kn) empty_dirpath (label_of_id id) in 
  let mib = Global.lookup_mind kn in 
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
let projs = ref Refset.empty

let add_record kn l = 
  records := KNmap.add kn l !records; 
  projs := List.fold_right Refset.add l !projs

let find_projections kn = KNmap.find kn !records
let is_projection r = Refset.mem r !projs

(*s Tables synchronization. *)

let freeze () = !terms, !types, !inductives, !recursors, !records, !projs

let unfreeze (te,ty,id,re,rd,pr) = 
  terms:=te; types:=ty; inductives:=id; recursors:=re; records:=rd; projs:=pr

let _ = declare_summary "Extraction tables"
	  { freeze_function = freeze;
	    unfreeze_function = unfreeze;
	    init_function = (fun () -> ());
	    survive_section = true }





