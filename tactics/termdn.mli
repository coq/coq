
(* $Id$ *)

(*i*)
open Generic
open Term
open Rawterm
(*i*)
  
(* Discrimination nets of terms. *)

(* This module registers actions (typically tactics) mapped to patterns *)

(* Patterns are stocked linearly as the list of its node in prefix
order in such a way patterns having the same prefix have this common
prefix shared and the seek for the action associated to the patterns
that a term matches are found in time proportional to the maximal
number of nodes of the patterns matching the term *)

type 'a t

val create : unit -> 'a t

(* [add t (c,a)] adds to table [t] pattern [c] associated to action [act] *)

val add : 'a t -> (constr_pattern * 'a) -> 'a t

val rmv : 'a t -> (constr_pattern * 'a) -> 'a t

(* [lookup t c] looks for patterns (with their action) matching term [c] *)

val lookup : 'a t -> constr -> (constr_pattern * 'a) list

val app : ((constr_pattern * 'a) -> unit) -> 'a t -> unit


(*i*)
(* These are for Nbtermdn *)

val constr_pat_discr : 
  constr_pattern -> (constr_label * constr_pattern list) option
val constr_val_discr :
  constr -> (constr_label * constr list) option

(*i*)
