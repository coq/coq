(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Pp
open Names
open Libnames
open Rawterm
open Libobject
open Lib
open Nameops

(* Syntactic definitions. *)

let syntax_table = ref (KNmap.empty : rawconstr KNmap.t)

let _ = Summary.declare_summary
	  "SYNTAXCONSTANT"
	  { Summary.freeze_function = (fun () -> !syntax_table);
	    Summary.unfreeze_function = (fun ft -> syntax_table := ft);
	    Summary.init_function = (fun () -> syntax_table := KNmap.empty);
	    Summary.survive_section = false }

let add_syntax_constant kn c =
  syntax_table := KNmap.add kn c !syntax_table

let cache_syntax_constant ((sp,kn),c) =
  if Nametab.exists_cci sp then
    errorlabstrm "cache_syntax_constant"
      (pr_id (basename sp) ++ str " already exists");
  add_syntax_constant kn c;
  Nametab.push_syntactic_definition (Nametab.Until 1) sp kn

let load_syntax_constant i ((sp,kn),c) =
  if Nametab.exists_cci sp then
    errorlabstrm "cache_syntax_constant"
      (pr_id (basename sp) ++ str " already exists");
  add_syntax_constant kn c;
  Nametab.push_syntactic_definition (Nametab.Until i) sp kn

let open_syntax_constant i ((sp,kn),c) =
  Nametab.push_syntactic_definition (Nametab.Exactly i) sp kn

let subst_syntax_constant ((sp,kn),subst,c) =
  subst_raw subst c

let classify_syntax_constant (_,c) = Substitute c

let (in_syntax_constant, out_syntax_constant) =
  declare_object {(default_object "SYNTAXCONSTANT") with
    cache_function = cache_syntax_constant;
    load_function = load_syntax_constant;
    open_function = open_syntax_constant;
    subst_function = subst_syntax_constant;
    classify_function = classify_syntax_constant;
    export_function = (fun x -> Some x) } 

let declare_syntactic_definition id c =
  let _ = add_leaf id (in_syntax_constant c) in ()

let search_syntactic_definition kn = KNmap.find kn !syntax_table
