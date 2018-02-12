(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Compatibility file for making Coq act similar to Coq v8.6 *)
Local Set Warnings Append "-masking-absolute-name".
Require Export Coq.Compat.Coq87.

Require Export Coq.extraction.Extraction.
Require Export Coq.funind.FunInd.
