(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* ML names *)

open Vernacexpr
open Pcoq
open Genarg

let wit_mlname, rawwit_mlname = Genarg.create_arg "mlname"
let mlname = create_generic_entry "mlname" rawwit_mlname
let _ = Tacinterp.add_genarg_interp "mlname"
  (fun ist x ->
    (in_gen wit_mlname
      (out_gen wit_string
	(Tacinterp.genarg_interp ist
	  (in_gen rawwit_string
	    (out_gen rawwit_mlname x))))))

GEXTEND Gram
  GLOBAL: mlname;
  mlname:
  [ [ id = IDENT -> id
    | s = STRING -> s ] ]
  ;
END

(* Extraction commands *)

open Table
open Extract_env
open Pcoq.Constr
open Pcoq.Prim

VERNAC COMMAND EXTEND Extraction
(* Extraction in the Coq toplevel *)
| [ "Extraction" constr(c) ] -> [ extraction c ]
| [ "Recursive" "Extraction" ne_qualid_list(l) ] -> [ extraction_rec l ]

(* Monolithic extraction to a file *)
| [ "Extraction" string(f) ne_qualid_list(l) ] 
  -> [ extraction_file f l ]

(* Modular extraction (one Coq module = one ML module) *)
| [ "Extraction" "Module" ident(m) ]
  -> [ extraction_module m ]
| [ "Recursive" "Extraction" "Module" ident(m) ]
  -> [ recursive_extraction_module m ]

(* Target Language *)

| [ "Extraction" "Language" "Ocaml" ] 
  -> [ extraction_language Ocaml ]
| [ "Extraction" "Language" "Haskell" ] 
  -> [ extraction_language Haskell ]
| [ "Extraction" "Language" "Toplevel" ] 
  -> [ extraction_language Toplevel ]

(* Custom inlining directives *)
| [ "Extraction" "Inline" ne_qualid_list(l) ] 
  -> [ extraction_inline true l ]

| [ "Extraction" "NoInline" ne_qualid_list(l) ] 
  -> [ extraction_inline false l ]

| [ "Print" "Extraction" "Inline" ]
  -> [ print_extraction_inline () ]

| [ "Reset" "Extraction" "Inline" ]
  -> [ reset_extraction_inline () ]

(* Overriding of a Coq object by an ML one *)
| [ "Extract" "Constant" qualid(x) "=>" mlname(y) ]
  -> [ extract_constant_inline false x y ]

| [ "Extract" "Inlined" "Constant" qualid(x) "=>" mlname(y) ]
  -> [ extract_constant_inline true x y ]

| [ "Extract" "Inductive" qualid(x) "=>" mlname(id) "[" mlname_list(idl) "]" ]
  -> [ extract_inductive x (id,idl) ]


END
