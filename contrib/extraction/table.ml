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
	[< Printer.pr_global r; 'sPC; 'sTR "is not a constant" >] 

let string_of_varg = function
  | VARG_IDENTIFIER id -> string_of_id id
  | VARG_STRING s -> s
  | _ -> assert false

let no_such_reference q =
  errorlabstrm "reference_of_varg" 
    [< Nametab.pr_qualid q; 'sTR ": no such reference" >]

let reference_of_varg = function
  | VARG_QUALID q -> 
      (try Nametab.locate q with Not_found -> no_such_reference q)
  | _ -> assert false

let refs_of_vargl = List.map reference_of_varg


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

let _ = 
  vinterp_add "ExtractionInline"
    (fun vl () -> 
       let refs = List.map check_constant (refs_of_vargl vl) in 
       add_anonymous_leaf (inline_extraction (true,refs)))

let _ = 
  vinterp_add "ExtractionNoInline"
    (fun vl () -> 
       let refs = List.map check_constant (refs_of_vargl vl) in 
       add_anonymous_leaf (inline_extraction (false,refs)))

(*s Printing part *)

let print_inline () = 
  let (i,n)= !inline_table in 
  let i'= Refset.filter is_constant i in 
  mSG 
    [< 'sTR "Extraction Inline:"; 'fNL; 
       Refset.fold
	 (fun r p -> [< p; 'sTR "   " ; Printer.pr_global r ; 'fNL >]) i' [<>];
       'sTR "Extraction NoInline:"; 'fNL; 
       Refset.fold
	 (fun r p -> [< p; 'sTR "   " ; Printer.pr_global r ; 'fNL >]) n [<>]
    >]

let _ = vinterp_add "PrintExtractionInline" (fun _ -> print_inline)


(*s Reset part *)

let (reset_inline,_) = 
  declare_object
    ("Reset Extraction Inline", 
     {  cache_function = (fun (_,_)-> inline_table :=  empty_inline_table);
	load_function = (fun (_,_)-> inline_table :=  empty_inline_table); 
	open_function = (fun _ -> ());
	export_function = (fun x -> Some x) })
	
let _ = vinterp_add "ResetExtractionInline" 
	  (fun _ () -> add_anonymous_leaf (reset_inline ()))
	  

(*s Table for direct ML extractions. *)

let empty_extractions = (Refmap.empty, Refset.empty, [])

let extractions = ref empty_extractions

let ml_extractions () = let (_,set,_) =  !extractions in set 

let sorted_ml_extractions () = let (_,_,l) = !extractions in l

let add_ml_extraction r s = 
  let (map,set,list) = !extractions in
  let list' = if (is_constant r) then (r,s)::list else list in 
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

let _ = 
  vinterp_add "ExtractConstant"
    (function 
       | [id; vs] -> 
	   (fun () -> 
	      let r = check_constant (reference_of_varg id) in 
	      let s = string_of_varg vs in 
	      add_anonymous_leaf (inline_extraction (false,[r]));
	      add_anonymous_leaf (in_ml_extraction (r,s)))
       | _ -> assert false)

let _ = 
  vinterp_add "ExtractInlinedConstant"
    (function 
       | [id; vs] -> 
	   (fun () -> 
	      let r = check_constant (reference_of_varg id) in 
	      let s = string_of_varg vs in 
	      add_anonymous_leaf (inline_extraction (true,[r]));
	      add_anonymous_leaf (in_ml_extraction (r,s)))
       | _ -> assert false)


let extract_inductive r (id2,l2) = match r with
  | IndRef ((sp,i) as ip) ->
      let mib = Global.lookup_mind sp in
      let n = Array.length mib.mind_packets.(i).mind_consnames in
      if n <> List.length l2 then
	error "not the right number of constructors";
      add_anonymous_leaf (in_ml_extraction (r,id2));
      list_iter_i
	(fun j s -> 
	   let r = ConstructRef (ip,succ j) in 
	   add_anonymous_leaf (inline_extraction (true,[r]));
	   add_anonymous_leaf (in_ml_extraction (r,s))) l2
  | _ -> 
      errorlabstrm "extract_inductive"
	[< Printer.pr_global r; 'sPC; 'sTR "is not an inductive type" >]

let _ = 
  vinterp_add "ExtractInductive"
    (function 
       | [q1; VARG_VARGLIST (id2 :: l2)] ->
	   (fun () -> 
	      extract_inductive (reference_of_varg q1) 
		(string_of_varg id2, List.map string_of_varg l2))
       | _ -> assert false)

