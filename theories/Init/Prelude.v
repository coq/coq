(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export Notations.
Require Export Logic.
Require Export Datatypes.
Require Export Specif.
Require Export Peano.
Require Export Coq.Init.Wf.
Require Export Coq.Init.Tactics.
(* Initially available plugins
   (+ nat_syntax_plugin loaded in Datatypes) *)
Declare ML Module "extraction_plugin".
Declare ML Module "decl_mode_plugin".
Declare ML Module "cc_plugin".
Declare ML Module "ground_plugin".
Declare ML Module "dp_plugin".
Declare ML Module "recdef_plugin".
Declare ML Module "subtac_plugin".
Declare ML Module "xml_plugin".