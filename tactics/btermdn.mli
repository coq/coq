
(* $Id$ *)

(*i*)
open Generic
open Term
(*i*)

(* Discrimination nets with bounded depth. *)

type 'a t

val create : unit -> 'a t

val add : 'a t -> (constr * 'a) -> 'a t
val rmv : 'a t -> (constr * 'a) -> 'a t

val lookup : 'a t -> constr -> (constr * 'a) list
val app : ((constr * 'a) -> unit) -> 'a t -> unit

val dnet_depth : int ref
