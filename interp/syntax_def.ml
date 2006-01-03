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

let syntax_table = ref (KNmap.empty : aconstr KNmap.t)

let _ = Summary.declare_summary
	  "SYNTAXCONSTANT"
	  { Summary.freeze_function = (fun () -> !syntax_table);
	    Summary.unfreeze_function = (fun ft -> syntax_table := ft);
	    Summary.init_function = (fun () -> syntax_table := KNmap.empty);
	    Summary.survive_module = false;
	    Summary.survive_section = false }

let add_syntax_constant kn c =
  syntax_table := KNmap.add kn c !syntax_table

let load_syntax_constant i ((sp,kn),(local,c,onlyparse)) =
  if Nametab.exists_cci sp then
    errorlabstrm "cache_syntax_constant"
      (pr_id (basename sp) ++ str " already exists");
  add_syntax_constant kn c;
  Nametab.push_syntactic_definition (Nametab.Until i) sp kn;
  if not onlyparse then
    (* Declare it to be used as (long) name *)
    Symbols.declare_uninterpretation (Symbols.SynDefRule kn) ([],c)

let open_syntax_constant i ((sp,kn),(_,c,onlyparse)) =
  Nametab.push_syntactic_definition (Nametab.Exactly i) sp kn;
  if not onlyparse then
    (* Redeclare it to be used as (short) name in case an other (distfix)
       notation was declared inbetween *)
    Symbols.declare_uninterpretation (Symbols.SynDefRule kn) ([],c)

let cache_syntax_constant d =
  load_syntax_constant 1 d

let subst_syntax_constant ((sp,kn),subst,(local,c,onlyparse)) =
  (local,subst_aconstr subst c,onlyparse)

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

let declare_syntactic_definition local id onlyparse c =
  let _ = add_leaf id (in_syntax_constant (local,c,onlyparse)) in ()

let rec set_loc loc _ a =
  rawconstr_of_aconstr_with_binders loc (fun id e -> (id,e)) (set_loc loc) () a

let search_syntactic_definition loc kn =
  set_loc loc () (KNmap.find kn !syntax_table)
