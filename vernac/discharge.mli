(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Declarations
open Entries
open Opaqueproof

val process_inductive :
  ((Term.constr, Term.constr) Context.Named.pt * Univ.abstract_universe_context)
  -> work_list -> mutual_inductive_body -> mutual_inductive_entry
