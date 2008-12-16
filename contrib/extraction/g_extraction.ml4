(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* ML names *)

open Vernacexpr
open Pcoq
open Genarg
open Pp

let pr_mlname _ _ _ s = spc () ++ qs s

ARGUMENT EXTEND mlname
  TYPED AS string
  PRINTED BY pr_mlname
| [ preident(id) ] -> [ id ]
| [ string(s) ] -> [ s ]
END

open Table
open Extract_env

let pr_language = function
  | Ocaml -> str "Ocaml" 
  | Haskell -> str "Haskell"
  | Scheme -> str "Scheme"

VERNAC ARGUMENT EXTEND language
PRINTED BY pr_language
| [ "Ocaml" ] -> [ Ocaml ]
| [ "Haskell" ] -> [ Haskell ]
| [ "Scheme" ] -> [ Scheme ]
END

(* Extraction commands *)

VERNAC COMMAND EXTEND Extraction
(* Extraction in the Coq toplevel *)
| [ "Extraction" global(x) ] -> [ simple_extraction x ]
| [ "Recursive" "Extraction" ne_global_list(l) ] -> [ full_extraction None l ]

(* Monolithic extraction to a file *)
| [ "Extraction" string(f) ne_global_list(l) ] 
  -> [ full_extraction (Some f) l ]
END

(* Modular extraction (one Coq library = one ML module) *)
VERNAC COMMAND EXTEND ExtractionLibrary
| [ "Extraction" "Library" ident(m) ]
  -> [ extraction_library false m ]
END

VERNAC COMMAND EXTEND RecursiveExtractionLibrary
| [ "Recursive" "Extraction" "Library" ident(m) ]
  -> [ extraction_library true m ]
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

VERNAC COMMAND EXTEND ExtractionBlacklist
(* Force Extraction to not use some filenames *)
| [ "Extraction" "Blacklist" ne_ident_list(l) ]
  -> [ extraction_blacklist l ]
END

VERNAC COMMAND EXTEND PrintExtractionBlacklist
| [ "Print" "Extraction" "Blacklist" ]
  -> [ print_extraction_blacklist () ]
END

VERNAC COMMAND EXTEND ResetExtractionBlacklist
| [ "Reset" "Extraction" "Blacklist" ]
  -> [ reset_extraction_blacklist () ]
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
