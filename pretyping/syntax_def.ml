(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Names
open Rawterm
open Libobject
open Lib

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

(* Impossible de rendre récursive la définition de in_syntax_constant
   et cache_syntax_constant, alors on triche ... *)
let cache_syntax_constant = ref (fun c -> failwith "Undefined function")

let (in_syntax_constant, out_syntax_constant) =
  let od = {
    cache_function = (fun c -> !cache_syntax_constant c);
    load_function = (fun _ -> ());
    open_function = (fun c -> !cache_syntax_constant c);
    export_function = (fun x -> Some x) } 
  in
  declare_object ("SYNTAXCONSTANT", od)

let _ =
  cache_syntax_constant := fun (sp,c) ->
    add_syntax_constant sp c;
    Nametab.push_object sp (in_syntax_constant c)

let declare_syntactic_definition id c =
  let _ = add_leaf id CCI (in_syntax_constant c) in ()

let search_syntactic_definition sp = Spmap.find sp !syntax_table

let locate_syntactic_definition sp =
  let (sp,obj) = Nametab.locate_obj sp in
  if object_tag obj = "SYNTAXCONSTANT" then sp else raise Not_found
  

