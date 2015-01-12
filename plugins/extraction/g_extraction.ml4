(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

(* ML names *)

open Genarg
open Pp
open Names
open Nameops
open Table
open Extract_env

let pr_mlname _ _ _ s = spc () ++ qs s

ARGUMENT EXTEND mlname
  TYPED AS string
  PRINTED BY pr_mlname
| [ preident(id) ] -> [ id ]
| [ string(s) ] -> [ s ]
END

let pr_int_or_id _ _ _ = function
  | ArgInt i -> int i
  | ArgId id -> pr_id id

ARGUMENT EXTEND int_or_id
  TYPED AS int_or_id
  PRINTED BY pr_int_or_id
| [ preident(id) ] -> [ ArgId (Id.of_string id) ]
| [ integer(i) ] -> [ ArgInt i ]
END

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

VERNAC COMMAND EXTEND Extraction CLASSIFIED AS QUERY
(* Extraction in the Coq toplevel *)
| [ "Extraction" global(x) ] -> [ simple_extraction x ]
| [ "Recursive" "Extraction" ne_global_list(l) ] -> [ full_extraction None l ]

(* Monolithic extraction to a file *)
| [ "Extraction" string(f) ne_global_list(l) ]
  -> [ full_extraction (Some f) l ]
END

VERNAC COMMAND EXTEND SeparateExtraction CLASSIFIED AS QUERY
(* Same, with content splitted in several files *)
| [ "Separate" "Extraction" ne_global_list(l) ]
  -> [ separate_extraction l ]
END

(* Modular extraction (one Coq library = one ML module) *)
VERNAC COMMAND EXTEND ExtractionLibrary CLASSIFIED AS QUERY
| [ "Extraction" "Library" ident(m) ]
  -> [ extraction_library false m ]
END

VERNAC COMMAND EXTEND RecursiveExtractionLibrary CLASSIFIED AS QUERY
| [ "Recursive" "Extraction" "Library" ident(m) ]
  -> [ extraction_library true m ]
END

(* Target Language *)
VERNAC COMMAND EXTEND ExtractionLanguage CLASSIFIED AS SIDEFF
| [ "Extraction" "Language" language(l) ]
  -> [ extraction_language l ]
END

VERNAC COMMAND EXTEND ExtractionInline CLASSIFIED AS SIDEFF
(* Custom inlining directives *)
| [ "Extraction" "Inline" ne_global_list(l) ]
  -> [ extraction_inline true l ]
END

VERNAC COMMAND EXTEND ExtractionNoInline CLASSIFIED AS SIDEFF
| [ "Extraction" "NoInline" ne_global_list(l) ]
  -> [ extraction_inline false l ]
END

VERNAC COMMAND EXTEND PrintExtractionInline CLASSIFIED AS QUERY
| [ "Print" "Extraction" "Inline" ]
  -> [ msg_info (print_extraction_inline ()) ]
END

VERNAC COMMAND EXTEND ResetExtractionInline CLASSIFIED AS SIDEFF
| [ "Reset" "Extraction" "Inline" ]
  -> [ reset_extraction_inline () ]
END

VERNAC COMMAND EXTEND ExtractionImplicit CLASSIFIED AS SIDEFF
(* Custom implicit arguments of some csts/inds/constructors *)
| [ "Extraction" "Implicit" global(r) "[" int_or_id_list(l) "]" ]
  -> [ extraction_implicit r l ]
END

VERNAC COMMAND EXTEND ExtractionBlacklist CLASSIFIED AS SIDEFF
(* Force Extraction to not use some filenames *)
| [ "Extraction" "Blacklist" ne_ident_list(l) ]
  -> [ extraction_blacklist l ]
END

VERNAC COMMAND EXTEND PrintExtractionBlacklist CLASSIFIED AS QUERY
| [ "Print" "Extraction" "Blacklist" ]
  -> [ msg_info (print_extraction_blacklist ()) ]
END

VERNAC COMMAND EXTEND ResetExtractionBlacklist CLASSIFIED AS SIDEFF
| [ "Reset" "Extraction" "Blacklist" ]
  -> [ reset_extraction_blacklist () ]
END


(* Overriding of a Coq object by an ML one *)
VERNAC COMMAND EXTEND ExtractionConstant CLASSIFIED AS SIDEFF
| [ "Extract" "Constant" global(x) string_list(idl) "=>" mlname(y) ]
  -> [ extract_constant_inline false x idl y ]
END

VERNAC COMMAND EXTEND ExtractionInlinedConstant CLASSIFIED AS SIDEFF
| [ "Extract" "Inlined" "Constant" global(x) "=>" mlname(y) ]
  -> [ extract_constant_inline true x [] y ]
END

VERNAC COMMAND EXTEND ExtractionInductive CLASSIFIED AS SIDEFF
| [ "Extract" "Inductive" global(x) "=>"
    mlname(id) "[" mlname_list(idl) "]" string_opt(o) ]
  -> [ extract_inductive x id idl o ]
END
