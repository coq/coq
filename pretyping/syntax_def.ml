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
open Rawterm
open Libobject
open Lib
open Nameops

(* Syntactic definitions. *)

let syntax_table = ref (Spmap.empty : rawconstr Spmap.t)

let _ = Summary.declare_summary
	  "SYNTAXCONSTANT"
	  { Summary.freeze_function = (fun () -> !syntax_table);
	    Summary.unfreeze_function = (fun ft -> syntax_table := ft);
	    Summary.init_function = (fun () -> syntax_table := Spmap.empty);
	    Summary.survive_section = false }

let add_syntax_constant sp c =
  syntax_table := Spmap.add sp c !syntax_table

let cache_syntax_constant (sp,c) =
  if Nametab.exists_cci sp then
    errorlabstrm "cache_syntax_constant"
      (pr_id (basename sp) ++ str " already exists");
  add_syntax_constant sp c;
  Nametab.push_syntactic_definition sp;
  Nametab.push_short_name_syntactic_definition sp

let load_syntax_constant (sp,c) =
  if Nametab.exists_cci sp then
    errorlabstrm "cache_syntax_constant"
      (pr_id (basename sp) ++ str " already exists");
  add_syntax_constant sp c;
  Nametab.push_syntactic_definition sp

let open_syntax_constant (sp,c) =
  Nametab.push_short_name_syntactic_definition sp

let (in_syntax_constant, out_syntax_constant) =
  let od = {
    cache_function = cache_syntax_constant;
    load_function = load_syntax_constant;
    open_function = open_syntax_constant;
    export_function = (fun x -> Some x) } 
  in
  declare_object ("SYNTAXCONSTANT", od)

let declare_syntactic_definition id c =
  let _ = add_leaf id (in_syntax_constant c) in ()

let search_syntactic_definition sp = Spmap.find sp !syntax_table

let locate_syntactic_definition qid =
  match Nametab.extended_locate qid with
    | Nametab.SyntacticDef sp -> sp
    | _ -> raise Not_found
