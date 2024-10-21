(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val wit_firstorder_using :
  (Libnames.qualid list, Names.GlobRef.t Loc.located Locus.or_var list,
   Names.GlobRef.t list)
  Genarg.genarg_type

val firstorder_using : Libnames.qualid list Procq.Entry.t
