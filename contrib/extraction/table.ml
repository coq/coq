(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Summary
open Lib
open Libobject
open Goptions
open Vernacinterp
open Extend
open Names
open Util
open Pp
open Term 
open Declarations
open Nametab

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
  declare_object ("Extraction Lang", 
		  {cache_function = (fun (_,l) -> lang_ref := l);
		   load_function = (fun (_,l) -> lang_ref := l);
		   open_function = (fun _ -> ());
		   export_function = (fun x -> Some x) })

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
  declare_object ("Extraction Inline",
		  { cache_function = (fun (_,(b,l)) -> add_inline_entries b l);
		    load_function = (fun (_,(b,l)) -> add_inline_entries b l);
		    open_function = (fun _ -> ());
		    export_function = (fun x -> Some x) })

let _ = declare_summary "Extraction Inline"
	  { freeze_function = (fun () -> !inline_table);
	    unfreeze_function = ((:=) inline_table);
	    init_function = (fun () -> inline_table := empty_inline_table);
	    survive_section = true }

(*s Grammar entries. *)

let extraction_inline b vl =
  let refs = List.map (fun x -> check_constant (Nametab.global x)) vl in 
  add_anonymous_leaf (inline_extraction (true,refs))

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
    ("Reset Extraction Inline", 
     {  cache_function = (fun (_,_)-> inline_table :=  empty_inline_table);
	load_function = (fun (_,_)-> inline_table :=  empty_inline_table); 
	open_function = (fun _ -> ());
	export_function = (fun x -> Some x) })

let reset_extraction_inline () = add_anonymous_leaf (reset_inline ())

(*s Table for direct ML extractions. *)

let empty_extractions = (Refmap.empty, Refset.empty, [])

let extractions = ref empty_extractions

let ml_extractions () = let (_,set,_) =  !extractions in set 

let sorted_ml_extractions () = let (_,_,l) = !extractions in l

let add_ml_extraction r s = 
  let (map,set,list) = !extractions in
  let list' = if (is_constant r) then 
    (r,s)::(List.remove_assoc r list) 
  else list in 
  extractions := (Refmap.add r s map, Refset.add r set, list')

let is_ml_extraction r = 
  let (_,set,_) = !extractions in Refset.mem r set

let find_ml_extraction r = 
  let (map,_,_) = !extractions in Refmap.find r map

(*s Registration of operations for rollback. *)

let (in_ml_extraction,_) = 
  declare_object ("ML extractions",
		  { cache_function = (fun (_,(r,s)) -> add_ml_extraction r s);
		    load_function = (fun (_,(r,s)) -> add_ml_extraction r s);
		    open_function = (fun _ -> ());
		    export_function = (fun x -> Some x) })

let _ = declare_summary "ML extractions"
	  { freeze_function = (fun () -> !extractions);
	    unfreeze_function = ((:=) extractions);
	    init_function = (fun () -> extractions := empty_extractions);
	    survive_section = true }


(*s Grammar entries. *)

let extract_constant_inline inline qid s =
  let r = check_constant (Nametab.global qid) in
  add_anonymous_leaf (inline_extraction (inline,[r]));
  add_anonymous_leaf (in_ml_extraction (r,s))

let extract_inductive r (id2,l2) =
  let r = Nametab.global r in match r with
  | IndRef ((sp,i) as ip) ->
      let mib = Global.lookup_mind sp in
      let n = Array.length mib.mind_packets.(i).mind_consnames in
      if n <> List.length l2 then
	error "Not the right number of constructors.";
      add_anonymous_leaf (in_ml_extraction (r,id2));
      list_iter_i
	(fun j s -> 
	   let r = ConstructRef (ip,succ j) in 
	   add_anonymous_leaf (inline_extraction (true,[r]));
	   add_anonymous_leaf (in_ml_extraction (r,s))) l2
  | _ -> 
      errorlabstrm "extract_inductive"
	(Printer.pr_global r ++ spc () ++ str "is not an inductive type.")
