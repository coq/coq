(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type vernac_toplevel =
  | VernacBacktrack of int * int * int
  | VernacDrop
  | VernacQuit
  | VernacControl of Vernacexpr.vernac_control

val vernac_toplevel : Pvernac.proof_mode option -> vernac_toplevel option Pcoq.Entry.t
