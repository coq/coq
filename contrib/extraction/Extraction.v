(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

Grammar vernac vernac : ast :=

(* Extraction in the Coq toplevel *)
  extr_constr [ "Extraction" constrarg($c) "." ] -> 
              [ (Extraction $c) ]
| extr_list   [ "Recursive" "Extraction" ne_qualidarg_list($l) "." ] ->
              [ (ExtractionRec ($LIST $l)) ]

(* Monolithic extraction to a file *)
| extr_file
     [ "Extraction" stringarg($f) ne_qualidarg_list($l) "." ] 
  -> [ (ExtractionFile "ocaml" $f ($LIST $l)) ]
| haskell_extr_file
     [ "Haskell" "Extraction" stringarg($f) ne_qualidarg_list($l) "." ] 
  -> [ (ExtractionFile "haskell" $f ($LIST $l)) ]

(* Modular extraction (one Coq module = one ML module) *)
| extr_module 
     [ "Extraction" "Module" identarg($m) "." ]
  -> [ (ExtractionModule "ocaml" $m) ]
| haskell_extr_module 
     [ "Haskell" "Extraction" "Module" identarg($m) "." ]
  -> [ (ExtractionModule "haskell" $m) ]

(* Custum inlining directives *)
| inline_constant
     [ "Extraction" "Inline" ne_qualidarg_list($l) "." ] 
  -> [ (ExtractionInline ($LIST $l)) ]
     
| no_inline_constant 
     [ "Extraction" "NoInline" ne_qualidarg_list($l) "." ] 
  -> [ (ExtractionNoInline ($LIST $l)) ]

(* Overriding of a Coq object by an ML one *)
| extract_constant 
     [ "Extract" "Constant" qualidarg($x) "=>" idorstring($y) "." ]
  -> [ (ExtractConstant $x $y) ]

| extract_inlined_constant 
     [ "Extract" "Inlined" "Constant" qualidarg($x) 
      "=>" idorstring($y) "." ]
  -> [ (ExtractInlinedConstant $x $y) ]

| extract_inductive 
     [ "Extract" "Inductive" qualidarg($x) "=>" mindnames($y) "."]
  -> [ (ExtractInductive $x $y) ]

(* Utility entries *)
with mindnames : ast :=
  mlconstr [ idorstring($id) "[" idorstring_list($idl) "]" ]
        -> [(VERNACARGLIST $id ($LIST $idl))]

with idorstring_list: ast list :=
  ids_nil  [ ] -> [ ]
| ids_cons [ idorstring($x) idorstring_list($l) ] -> [ $x ($LIST $l) ]

with idorstring : ast :=
  ids_ident  [ identarg($id) ] -> [ $id ]
| ids_string [ stringarg($s) ] -> [ $s ]
.