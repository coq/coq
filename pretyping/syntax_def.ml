
(* $Id$ *)

open Names
open Rawterm
open Libobject
open Lib

(* Syntactic definitions. *)

let syntax_table = ref (Idmap.empty : rawconstr Idmap.t)

let _ = Summary.declare_summary
	  "SYNTAXCONSTANT"
	  { Summary.freeze_function = (fun () -> !syntax_table);
	    Summary.unfreeze_function = (fun ft -> syntax_table := ft);
	    Summary.init_function = (fun () -> syntax_table := Idmap.empty) }

let add_syntax_constant id c =
  syntax_table := Idmap.add id c !syntax_table

let cache_syntax_constant (sp,c) = 
  add_syntax_constant (basename sp) c;
  Nametab.push (basename sp) sp

let open_syntax_constant (sp,_) =
  Nametab.push (basename sp) sp

let (in_syntax_constant, out_syntax_constant) =
  let od = {
    cache_function = cache_syntax_constant;
    load_function = cache_syntax_constant;
    open_function = (fun _ -> ());
    specification_function = (fun x -> x) } 
  in
  declare_object ("SYNTAXCONSTANT", od)

let declare_syntactic_definition id c =
  let _ = add_leaf id CCI (in_syntax_constant c) in ()

let search_syntactic_definition id = Idmap.find id !syntax_table

