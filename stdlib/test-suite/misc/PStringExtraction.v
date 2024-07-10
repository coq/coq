(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Import Uint63 PrimString ExtrOCamlPString.

Local Open Scope uint63.
Local Open Scope pstring.

Definition s1 := "hello".
Definition s2 := "wwworlddd".

Definition s := cat s1 (cat ", " (cat (sub s2 2 5) "!")).

Definition w := make (length s) "w"%char63.

Definition c := compare s w.

Recursive Extraction c.
