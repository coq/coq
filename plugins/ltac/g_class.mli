(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val wit_debug : (bool, bool, bool) Genarg.genarg_type

val debug : bool Procq.Entry.t

val wit_eauto_search_strategy_name :
  (Class_tactics.search_strategy, Class_tactics.search_strategy,
   Class_tactics.search_strategy)
  Genarg.genarg_type

val eauto_search_strategy_name : Class_tactics.search_strategy Procq.Entry.t

val wit_eauto_search_strategy :
  (Class_tactics.search_strategy option,
   Class_tactics.search_strategy option,
   Class_tactics.search_strategy option)
  Genarg.genarg_type

val eauto_search_strategy : Class_tactics.search_strategy option Procq.Entry.t
