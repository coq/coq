module Stage :
sig
  type var
  type t = Infty | StageVar of var * int
  val compare : t -> t -> int
  val show : t -> string
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
  type vars
  type t = Stage.var * vars * vars
  val mem : Stage.var -> vars -> bool
  val init : t
  val get_vars : t -> vars
  val get_pos_vars : t -> vars
  val next : ?s:Annot.t -> t -> Annot.t * t
  val show : t -> string
  val pr : t -> Pp.t
end

module Constraints :
sig
  module Set : CSig.SetS
  type t
  type 'a constrained = 'a * t
  val empty : t
  val union : t -> t -> t
  val union_list : t list -> t
  val add : Annot.t -> Annot.t -> t -> t
  val tos : Stage.t -> t -> Set.t
  val froms : Stage.t -> t -> Set.t
  val show : t -> string
  val pr : t -> Pp.t
end
