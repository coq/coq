(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Term
open Pattern
open Libnames
open Names
(*i*)
  
(* Discrimination nets of terms. *)

(* This module registers actions (typically tactics) mapped to patterns *)

(* Patterns are stocked linearly as the list of its node in prefix
order in such a way patterns having the same prefix have this common
prefix shared and the seek for the action associated to the patterns
that a term matches are found in time proportional to the maximal
number of nodes of the patterns matching the term. The [transparent_state] 
indicates which constants and variables can be considered as rigid.
These dnets are able to cope with existential variables as well, which match
[Everything]. *)

type 'a t

val create : unit -> 'a t

(* [add t (c,a)] adds to table [t] pattern [c] associated to action [act] *)

val add : 'a t -> transparent_state -> (constr_pattern * 'a) -> 'a t

val rmv : 'a t -> transparent_state -> (constr_pattern * 'a) -> 'a t

(* [lookup t c] looks for patterns (with their action) matching term [c] *)

val lookup : 'a t -> transparent_state -> constr -> (constr_pattern * 'a) list

val app : ((constr_pattern * 'a) -> unit) -> 'a t -> unit


(*i*)
(* These are for Nbtermdn *)

val constr_pat_discr_st : transparent_state ->
  constr_pattern -> (global_reference * constr_pattern list) option
val constr_val_discr_st : transparent_state ->
  constr -> (global_reference * constr list) Dn.lookup_res

val constr_pat_discr : constr_pattern -> (global_reference * constr_pattern list) option
val constr_val_discr : constr -> (global_reference * constr list) Dn.lookup_res

(*i*)
