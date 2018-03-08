(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pcoq.Prim

DECLARE PLUGIN "extraction_plugin"

(* ML names *)

open Ltac_plugin
open Genarg
open Stdarg
open Pp
open Names
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
  | ArgId id -> Id.print id

ARGUMENT EXTEND int_or_id
  PRINTED BY pr_int_or_id
| [ preident(id) ] -> [ ArgId (Id.of_string id) ]
| [ integer(i) ] -> [ ArgInt i ]
END

let pr_language = function
  | Ocaml -> str "OCaml"
  | Haskell -> str "Haskell"
  | Scheme -> str "Scheme"
  | JSON -> str "JSON"

let warn_deprecated_ocaml_spelling =
  CWarnings.create ~name:"deprecated-ocaml-spelling" ~category:"deprecated"
    (fun () ->
      strbrk ("The spelling \"OCaml\" should be used instead of \"Ocaml\"."))

VERNAC ARGUMENT EXTEND language
PRINTED BY pr_language
| [ "Ocaml" ] -> [ let _ = warn_deprecated_ocaml_spelling () in Ocaml ]
| [ "OCaml" ] -> [ Ocaml ]
| [ "Haskell" ] -> [ Haskell ]
| [ "Scheme" ] -> [ Scheme ]
| [ "JSON" ] -> [ JSON ]
END

(* Extraction commands *)

VERNAC COMMAND EXTEND Extraction CLASSIFIED AS QUERY
(* Extraction in the Coq toplevel *)
| [ "Extraction" global(x) ] -> [ simple_extraction x ]
| [ "Recursive" "Extraction" ne_global_list(l) ] -> [ full_extraction None l ]

(* Monolithic extraction to a file *)
| [ "Extraction" string(f) ne_global_list(l) ]
  -> [ full_extraction (Some f) l ]

(* Extraction to a temporary file and OCaml compilation *)
| [ "Extraction" "TestCompile" ne_global_list(l) ]
  -> [ extract_and_compile l ]
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
  -> [Feedback. msg_info (print_extraction_inline ()) ]
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
  -> [ Feedback.msg_info (print_extraction_blacklist ()) ]
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
(* Show the extraction of the current proof *)

VERNAC COMMAND EXTEND ShowExtraction CLASSIFIED AS QUERY
| [ "Show" "Extraction" ]
  -> [ show_extraction () ]
END
