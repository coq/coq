module SVars :
sig
  type t
  type var = int
  val empty : t
  val is_empty : t -> bool
  val add : var -> t -> t
  val mem : var -> t -> bool
  val union : t -> t -> t
  val union_list : t list -> t
  val inter : t -> t -> t
  val diff : t -> t -> t
  val fold : (var -> 'a -> 'a) -> t -> 'a -> 'a
  val pr : string -> t -> Pp.t
end

module Stage :
sig
  type t = Infty | StageVar of SVars.var * int
  val compare : t -> t -> int
end

module Annot :
sig
  type t = Empty | Star | Glob | Stage of Stage.t
  val infty : t
  val hat : t -> t
  val is_stage : t -> bool
  val compare : t -> t -> int
  val show : t -> string
  val pr : t -> Pp.t
  val hash : t -> int
end

module State :
sig
  type t
  val init : t
  val push : t -> t
  val pop : t -> t
  val get_vars : t -> SVars.t
  val get_pos_vars : t -> SVars.t
  val remove_pos_vars : SVars.t -> t -> t
  val next : ?s:Annot.t -> t -> Annot.t * t
  val pr : t -> Pp.t
end

module Constraints :
sig
  type t
  type 'a constrained = 'a * t
  val fold : (SVars.var -> SVars.var -> int -> 'a -> 'a) -> t -> 'a -> 'a
  val filter : (SVars.var -> SVars.var -> int -> bool) -> t -> t
  val empty : t
  val union : t -> t -> t
  val union_list : t list -> t
  val contains : SVars.var * SVars.var -> t -> bool
  val add : Annot.t -> Annot.t -> t -> t
  val add_infty : SVars.t -> t -> t
  val sup : SVars.var -> t -> SVars.t
  val sub : SVars.var -> t -> SVars.t
  val pr : t -> Pp.t
end

exception RecCheckFailed of Constraints.t * SVars.t * SVars.t

val bellman_ford_all : Constraints.t -> SVars.t

val downward : Constraints.t -> SVars.t -> SVars.t
val upward   : Constraints.t -> SVars.t -> SVars.t

val rec_check : SVars.var -> SVars.t -> SVars.t -> Constraints.t -> Constraints.t
