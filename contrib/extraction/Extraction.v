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
              [(Extraction $c)]
| extr_list   [ "Extraction" "-r" ne_qualidarg_list($l) "." ] ->
              [(ExtractionList ($LIST $l))].
