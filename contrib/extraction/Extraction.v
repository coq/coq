(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

Declare ML Module "mlutil.cmo" "ocaml.cmo" "extraction.cmo" "extract_env.cmo".

Grammar vernac vernac : ast :=
  extr_constr [ "Extraction" constrarg($c) "." ] -> 
              [ (Extraction $c) ]
| extr_list   [ "Recursive" "Extraction" ne_qualidarg_list($l) "." ] ->
              [ (ExtractionRec ($LIST $l)) ]
| extr_list   [ "Extraction" stringarg($f) ne_qualidarg_list($l) "." ] ->
              [ (ExtractionFile $f ($LIST $l)) ]
| extr_module [ "Extraction" "Module" identarg($m) "." ] ->
              [ (ExtractionModule $m) ].

