
(* $Id$ *)

(*i*)
open Generic
open Term
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

val add : 'a t -> (constr * 'a) -> 'a t

val rmv : 'a t -> (constr * 'a) -> 'a t

(* [lookup t c] looks for patterns (with their action) matching term [c] *)

val lookup : 'a t -> constr -> (constr * 'a) list

val app : ((constr * 'a) -> unit) -> 'a t -> unit


(*i*)
(* These are for Nbtermdn *)

type lbl =
  | TERM of constr
  | DOPER of sorts oper
  | DLAMBDA

val constr_pat_discr : constr -> (lbl * constr list) option
val constr_val_discr : constr -> (lbl * constr list) option

(*i*)
