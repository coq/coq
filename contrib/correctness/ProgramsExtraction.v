(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filli�tre *)

(* $Id$ *)

Require Export Extraction.

Extract Inductive unit => unit [ "()" ].
Extract Inductive bool => bool [ true false ].
Extract Inductive sumbool => bool [ true false ].

Require Export Correctness.

Declare ML Module "pextract".

Grammar vernac vernac : ast :=
  imperative_ocaml [ "Write" "Caml" "File" stringarg($file) 
    "[" ne_identarg_list($idl) "]" "." ]
     -> [ (IMPERATIVEEXTRACTION $file (VERNACARGLIST ($LIST $idl))) ]

| initialize [ "Initialize" identarg($id) "with" comarg($c) "." ]
     -> [ (INITIALIZE $id $c) ]
.
