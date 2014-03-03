(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Pattern
open Globnames
open Names

type term_label =
| GRLabel of global_reference
| ProdLabel
| LambdaLabel
| SortLabel

val compare_term_label : term_label -> term_label -> int

(** Discrimination nets of terms. *)

(** This module registers actions (typically tactics) mapped to patterns *)

(** Patterns are stocked linearly as the list of its node in prefix
order in such a way patterns having the same prefix have this common
prefix shared and the seek for the action associated to the patterns
that a term matches are found in time proportional to the maximal
number of nodes of the patterns matching the term. The [transparent_state]
indicates which constants and variables can be considered as rigid.
These dnets are able to cope with existential variables as well, which match
[Everything]. *)

(**/**)
(** These are for Nbtermdn *)

val constr_pat_discr_st : transparent_state ->
  constr_pattern -> (term_label * constr_pattern list) option
val constr_val_discr_st : transparent_state ->
  constr -> (term_label * constr list) Dn.lookup_res

val constr_pat_discr : constr_pattern -> (term_label * constr_pattern list) option
val constr_val_discr : constr -> (term_label * constr list) Dn.lookup_res
