
(* $Id$ *)

(*i*)
open Generic
open Term
(*i*)

(* Named, bounded-depth, term-discrimination nets. *)

type ('na,'a) t
type ('na,'a) frozen_t

val create : unit -> ('na,'a) t

val add : ('na,'a) t -> ('na * (constr * 'a)) -> unit
val rmv : ('na,'a) t -> 'na -> unit
val in_dn : ('na,'a) t -> 'na -> bool
val remap : ('na,'a) t -> 'na -> (constr * 'a) -> unit

val lookup : ('na,'a) t -> constr -> (constr * 'a) list
val app : ('na -> (constr * 'a) -> unit) -> ('na,'a) t -> unit

val dnet_depth : int ref

val freeze : ('na,'a) t -> ('na,'a) frozen_t
val unfreeze : ('na,'a) frozen_t -> ('na,'a) t -> unit
val empty : ('na,'a) t -> unit
val to2lists : ('na,'a) t -> ('na * (Term.constr * 'a)) list * 
                             (Termdn.lbl option * 'a Btermdn.t) list
