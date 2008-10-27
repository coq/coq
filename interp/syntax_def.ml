(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Pp
open Names
open Libnames
open Topconstr
open Libobject
open Lib
open Nameops

(* Syntactic definitions. *)

let syntax_table = ref (KNmap.empty : interpretation KNmap.t)

let _ = Summary.declare_summary
	  "SYNTAXCONSTANT"
	  { Summary.freeze_function = (fun () -> !syntax_table);
	    Summary.unfreeze_function = (fun ft -> syntax_table := ft);
	    Summary.init_function = (fun () -> syntax_table := KNmap.empty);
	    Summary.survive_module = false;
	    Summary.survive_section = false }

let add_syntax_constant kn c =
  syntax_table := KNmap.add kn c !syntax_table

let load_syntax_constant i ((sp,kn),(local,pat,onlyparse)) =
  if Nametab.exists_cci sp then
    errorlabstrm "cache_syntax_constant"
      (pr_id (basename sp) ++ str " already exists");
  add_syntax_constant kn pat;
  Nametab.push_syntactic_definition (Nametab.Until i) sp kn;
  if not onlyparse then
    (* Declare it to be used as long name *)
    Notation.declare_uninterpretation (Notation.SynDefRule kn) pat

let open_syntax_constant i ((sp,kn),(_,pat,onlyparse)) =
  Nametab.push_syntactic_definition (Nametab.Exactly i) sp kn;
  if not onlyparse then
    (* Redeclare it to be used as (short) name in case an other (distfix)
       notation was declared inbetween *)
    Notation.declare_uninterpretation (Notation.SynDefRule kn) pat

let cache_syntax_constant d =
  load_syntax_constant 1 d

let subst_syntax_constant ((sp,kn),subst,(local,pat,onlyparse)) =
  (local,subst_interpretation subst pat,onlyparse)

let classify_syntax_constant (_,(local,_,_ as o)) =
  if local then Dispose else Substitute o

let export_syntax_constant (local,_,_ as o) =
  if local then None else Some o

let (in_syntax_constant, out_syntax_constant) =
  declare_object {(default_object "SYNTAXCONSTANT") with
    cache_function = cache_syntax_constant;
    load_function = load_syntax_constant;
    open_function = open_syntax_constant;
    subst_function = subst_syntax_constant;
    classify_function = classify_syntax_constant;
    export_function = export_syntax_constant } 

type syndef_interpretation = (identifier * subscopes) list * aconstr

(* Coercions to the general format of notation that also supports
   variables bound to list of expressions *)
let in_pat (ids,ac) = ((ids,[]),ac)
let out_pat ((ids,idsl),ac) = assert (idsl=[]); (ids,ac)

let declare_syntactic_definition local id onlyparse pat =
  let _ = add_leaf id (in_syntax_constant (local,in_pat pat,onlyparse)) in ()

let search_syntactic_definition loc kn =
  out_pat (KNmap.find kn !syntax_table)

let locate_global_with_alias (loc,qid) =
  match Nametab.extended_locate qid with
  | TrueGlobal ref -> ref
  | SyntacticDef kn -> 
  match search_syntactic_definition dummy_loc kn with
  | [],ARef ref -> ref
  | _ -> 
      user_err_loc (loc,"",pr_qualid qid ++ 
        str " is bound to a notation that does not denote a reference")

let inductive_of_reference_with_alias r =
  match locate_global_with_alias (qualid_of_reference r) with
  | IndRef ind -> ind
  | ref ->
      user_err_loc (loc_of_reference r,"global_inductive",
        pr_reference r ++ spc () ++ str "is not an inductive type")

let global_with_alias r =
  let (loc,qid as lqid) = qualid_of_reference r in
  try locate_global_with_alias lqid
  with Not_found -> Nametab.error_global_not_found_loc loc qid
