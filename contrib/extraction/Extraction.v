(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

Declare ML Module "mlutil" "ocaml" "extraction" "extract_env".

Grammar vernac vernac : ast :=
  extr_constr [ "Extraction" constrarg($c) "." ] -> 
              [ (Extraction $c) ]
| extr_list   [ "Recursive" "Extraction" ne_qualidarg_list($l) "." ] ->
              [ (ExtractionRec ($LIST $l)) ]
| extr_list   [ "Extraction" stringarg($f) ne_qualidarg_list($l) "." ] ->
              [ (ExtractionFile $f ($LIST $l)) ]
| extr_module [ "Extraction" "Module" identarg($m) "." ] ->
              [ (ExtractionModule $m) ]

| extract_constant 
     [ "Extract" "Constant" qualidarg($x) "=>" idorstring($y) "." ]
  -> [ (EXTRACT_CONSTANT $x $y) ]

| extract_inductive 
     [ "Extract" "Inductive" qualidarg($x) "=>" mindnames($y) "."]
  -> [ (EXTRACT_INDUCTIVE $x $y) ]

with mindnames : ast :=
  mlconstr [ idorstring($id) "[" idorstring_list($idl) "]" ]
        -> [(VERNACARGLIST $id ($LIST $idl))]

with idorstring_list: List :=
  ids_nil  [ ] -> [ ]
| ids_cons [ idorstring($x) idorstring_list($l) ] -> [ $x ($LIST $l) ]

with idorstring : ast :=
  ids_ident  [ identarg($id) ] -> [ $id ]
| ids_string [ stringarg($s) ] -> [ $s ].
