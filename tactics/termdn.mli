
(* $Id$ *)

(*i*)
open Generic
open Term
(*i*)
  
(* Discrimination nets of terms. *)

type lbl =
  | TERM of constr
  | DOPER of sorts oper
  | DLAMBDA

type 'a t = (lbl,constr,'a) Dn.t

val create : unit -> 'a t

val add : 'a t -> (constr * 'a) -> 'a t
val rmv : 'a t -> (constr * 'a) -> 'a t

val lookup : 'a t -> constr -> (constr * 'a) list
val app : ((constr * 'a) -> unit) -> 'a t -> unit

val constr_pat_discr : constr -> (lbl * constr list) option
val constr_val_discr : constr -> (lbl * constr list) option
