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
open Pp

VERNAC ARGUMENT EXTEND mlname
| [ preident(id) ] -> [ id ]
| [ string(s) ] -> [ s ]
END

open Table
open Extract_env

VERNAC ARGUMENT EXTEND language
| [ "Ocaml" ] -> [ Ocaml ]
| [ "Haskell" ] -> [ Haskell ]
| [ "Scheme" ] -> [ Scheme ]
| [ "Toplevel" ] -> [ Toplevel ]
END

(* Extraction commands *)

VERNAC COMMAND EXTEND Extraction
(* Extraction in the Coq toplevel *)
| [ "Extraction" global(x) ] -> [ extraction x ]
| [ "Recursive" "Extraction" ne_global_list(l) ] -> [ extraction_rec l ]

(* Monolithic extraction to a file *)
| [ "Extraction" string(f) ne_global_list(l) ] 
  -> [ extraction_file f l ]
END

(* Extraction of a Coq module in the Coq toplevel *)
VERNAC COMMAND EXTEND ExtractionModule
| [ "Extraction" "Module" global(m) ] 
  -> [ extraction_module m ]   
END

(* Modular extraction (one Coq library = one ML module) *)
VERNAC COMMAND EXTEND ExtractionLibrary
| [ "Extraction" "Library" ident(m) ]
  -> [ extraction_library m ]
END

VERNAC COMMAND EXTEND RecursiveExtractionLibrary
| [ "Recursive" "Extraction" "Library" ident(m) ]
  -> [ recursive_extraction_library m ]
END

(* Target Language *)
VERNAC COMMAND EXTEND ExtractionLanguage
| [ "Extraction" "Language" language(l) ] 
  -> [ extraction_language l ]
END

VERNAC COMMAND EXTEND ExtractionInline
(* Custom inlining directives *)
| [ "Extraction" "Inline" ne_global_list(l) ] 
  -> [ extraction_inline true l ]
END

VERNAC COMMAND EXTEND ExtractionNoInline
| [ "Extraction" "NoInline" ne_global_list(l) ] 
  -> [ extraction_inline false l ]
END

VERNAC COMMAND EXTEND PrintExtractionInline
| [ "Print" "Extraction" "Inline" ]
  -> [ print_extraction_inline () ]
END

VERNAC COMMAND EXTEND ResetExtractionInline
| [ "Reset" "Extraction" "Inline" ]
  -> [ reset_extraction_inline () ]
END

(* Overriding of a Coq object by an ML one *)
VERNAC COMMAND EXTEND ExtractionConstant
| [ "Extract" "Constant" global(x) string_list(idl) "=>" mlname(y) ]
  -> [ extract_constant_inline false x idl y ]
END

VERNAC COMMAND EXTEND ExtractionInlinedConstant
| [ "Extract" "Inlined" "Constant" global(x) "=>" mlname(y) ]
  -> [ extract_constant_inline true x [] y ]
END

VERNAC COMMAND EXTEND ExtractionInductive
| [ "Extract" "Inductive" global(x) "=>" mlname(id) "[" mlname_list(idl) "]" ]
  -> [ extract_inductive x (id,idl) ]
END
