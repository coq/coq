(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Summary
open Libobject
open Goptions
open Lib
open Names
open Libnames
open Term
open Declarations
open Util
open Pp
open Reduction

(*s Warning and Error messages. *)

let error_axiom_scheme kn = 
  errorlabstrm "axiom_scheme_message" 
    (str "Extraction cannot accept the type scheme axiom " ++ spc () ++
     pr_kn kn ++ spc () ++ str ".") 

let error_axiom kn =
  errorlabstrm "axiom_message"
    (str "You must specify an extraction for axiom" ++ spc () ++ 
     pr_kn kn ++ spc () ++ str "first.")

let warning_axiom kn = 
  Options.if_verbose warn 
    (str "This extraction depends on logical axiom" ++ spc () ++ 
     pr_kn kn ++ str "." ++ spc() ++ 
     str "Having false logical axiom in the environment when extracting" ++ 
     spc () ++ str "may lead to incorrect or non-terminating ML terms.")
    
let error_section () = 
  errorlabstrm "section_message"
    (str "You can't do that within a section. Close it and try again.")

(*s AutoInline parameter *)

let auto_inline_ref = ref true

let auto_inline () = !auto_inline_ref

let _ = declare_bool_option 
	  {optsync = true;
	   optname = "Extraction AutoInline";
	   optkey = SecondaryTable ("Extraction", "AutoInline");
	   optread = auto_inline; 
	   optwrite = (:=) auto_inline_ref}

(*s Optimize parameter *)

let optim_ref = ref true

let optim () = !optim_ref 

let _ = declare_bool_option 
	  {optsync = true; 
	   optname = "Extraction Optimize";
	   optkey = SecondaryTable ("Extraction", "Optimize");
	   optread = optim; 
	   optwrite = (:=) optim_ref}


(*s Set and Map over global reference *)

module Refset = 
  Set.Make(struct type t = global_reference let compare = compare end)

module Refmap = 
  Map.Make(struct type t = global_reference let compare = compare end)

(*s Auxiliary functions *) 

let is_constant r = match r with 
  | ConstRef _ -> true
  | _ -> false

let check_constant r = 
  if (is_constant r) then r 
  else errorlabstrm "extract_constant"
	(Printer.pr_global r ++ spc () ++ str "is not a constant.") 

(*s Target Language *)

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

let extraction_language x = add_anonymous_leaf (extr_lang x)

(*s Table for custom inlining *)

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
  if sections_are_opened () then error_section (); 
  let refs = List.map (fun x -> check_constant (Nametab.global x)) l in 
  add_anonymous_leaf (inline_extraction (b,refs))

(*s Printing part *)

let print_extraction_inline () = 
  let (i,n)= !inline_table in 
  let i'= Refset.filter is_constant i in 
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

let reset_extraction_inline () = add_anonymous_leaf (reset_inline ())

(*s Table for direct ML extractions. *)

type kind = Term | Type | Ind | Construct 

let check_term_or_type r = match r with 
  | ConstRef sp -> 
      let env = Global.env () in 
      let typ = whd_betadeltaiota env (Environ.constant_type env sp) in 
      (match kind_of_term typ with 
	 | Sort _ -> (r,Type)
	 | _ -> if not (is_arity env typ) then (r,Term)
	   else errorlabstrm "extract_constant"
	     (Printer.pr_global r ++ spc () ++ 
	      str "is a type scheme, not a type."))
  | _ -> errorlabstrm "extract_constant"
	(Printer.pr_global r ++ spc () ++ str "is not a constant.") 

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
  if sections_are_opened () then error_section (); 
  let g,k = check_term_or_type (Nametab.global r) in
  add_anonymous_leaf (inline_extraction (inline,[g]));
  add_anonymous_leaf (in_ml_extraction (g,k,s))

let extract_inductive r (s,l) =
  if sections_are_opened () then error_section (); 
  let g = Nametab.global r in match g with
  | IndRef ((kn,i) as ip) ->
      let mib = Global.lookup_mind kn in
      let n = Array.length mib.mind_packets.(i).mind_consnames in
      if n <> List.length l then
	error "Not the right number of constructors.";
      add_anonymous_leaf (inline_extraction (true,[g]));
      add_anonymous_leaf (in_ml_extraction (g,Ind,s));
      list_iter_i
	(fun j s -> 
	   let g = ConstructRef (ip,succ j) in 
	   add_anonymous_leaf (inline_extraction (true,[g]));
	   add_anonymous_leaf (in_ml_extraction (g,Construct,s))) l
  | _ -> 
      errorlabstrm "extract_inductive"
	(Printer.pr_global g ++ spc () ++ str "is not an inductive type.")
