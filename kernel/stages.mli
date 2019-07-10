module Stage :
sig
  type var = int
  type t = Infty | StageVar of var * int
  val compare : t -> t -> int
end

module Annot :
sig
  type t = Empty | Star | Stage of Stage.t
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
  type vars = Int.Set.t
  type t = Stage.var * vars * vars
  val mem : Stage.var -> vars -> bool
  val diff : vars -> vars -> vars
  val init : t
  val get_vars : t -> vars
  val get_pos_vars : t -> vars
  val next : ?s:Annot.t -> t -> Annot.t * t
  val pr : t -> Pp.t
  val pr_vars : string -> vars -> Pp.t
end

module Constraints :
sig
  type t
  type 'a constrained = 'a * t
  val fold : (Stage.var -> Stage.var -> int -> 'a -> 'a) -> t -> 'a -> 'a
  val filter : (Stage.var -> Stage.var -> int -> bool) -> t -> t
  val empty : t
  val union : t -> t -> t
  val union_list : t list -> t
  val contains : Stage.var * Stage.var -> t -> bool
  val add : Annot.t -> Annot.t -> t -> t
  val sup : Stage.var -> t -> State.vars
  val sub : Stage.var -> t -> State.vars
  val pr : t -> Pp.t
end

exception RecCheckFailed of Constraints.t * State.vars * State.vars

val bellman_ford_all : Constraints.t -> State.vars

val downward : Constraints.t -> State.vars -> State.vars
val upward   : Constraints.t -> State.vars -> State.vars

val rec_check : Stage.var -> State.vars -> State.vars -> Constraints.t -> Constraints.t
