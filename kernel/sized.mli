(**
  A primer on the structure of sized types.

  Every (co)inductive type comes with an annotation, indicating whether it
  has a size, or whether it is in some special position.
    e.g. List^υ1 Nat^υ2 is the annotated type of a list of nats

  There are four types of annotations [Annot]:
    * Empty annotations: Before type-checking, inductive types carry no size
      information; we say that they are "bare" types.
        e.g. List° Nat°
    * Star annotations: These appear only in the types of (co)fixpoint terms.
      For fixpoints, they mark the position of the recursive argument,
      as well as possibly the return type to indicate that the size of the
      value returned is at most the size of the recursive argument.
        e.g. fix tail : List* Nat° -> List* Nat° := ...
      For cofixpoints, they must mark the return type, as well as possibly
      any arguments that have size at least that of the return type.
        e.g. cofix zip : Stream* Nat° -> Stream* Nat° -> Stream* Nat° := ...
      We also call these position annotations.
    * Size annotations: These contain size information.

  There are two types of sizes [Size]:
    * Infty: A (co)inductive type with infinite size is said to be a "full"
      type, and the same type with any other size is a sub-(or super-)type
      of the full inductive (or coinductive) type.
        e.g. ∀υ Nat^υ ≤ Nat^∞
    * SizeVar: A size containing a size variable and a successor value.
      Normally sizes are ordinals counting the constructor depth of a type,
      but in this system (CIC^) we merely need a size variable to be picked
      out of some set of enumerables, and add on the number of hats it has.
        e.g. ∀s s ⊑ ŝ, which we also write as (s+1)

  Although size variables can be any sort of enumerable, for convenience,
  we use the zero-inclusive naturals. Sets of size variables [SVars] are
  therefore simply IntSets.

  We use [State] to keep track of a few things:
    * The next size variable that we can use;
    * The set of all size variables used so far; and
    * The set of size variables corresponding to position annotations.
  The latter is important during type-checking of (co)fixpoints.

  Finally, we use [Constraints] to keep track of the size constraints induced
  by subtyping relations.
    e.g. List^υ1 Nat ≤ List^υ2 ⟹ υ1 ⊑ υ2
*)

module SVar :
sig
  type t = int (* Need to expose type for testing *)
  val infty : t
  val equal : t -> t -> bool
  val succ : t -> t
  val skip : int -> t -> t
end

module SVars :
sig
  type t
  val empty : t
  val is_empty : t -> bool
  val add : SVar.t -> t -> t
  val mem : SVar.t -> t -> bool
  val of_list : SVar.t list -> t
  val union : t -> t -> t
  val union_list : t list -> t
  val inter : t -> t -> t
  val diff : t -> t -> t
  val fold : (SVar.t -> 'a -> 'a) -> t -> 'a -> 'a
  val pr : t -> Pp.t
end

module Size :
sig
  type t = Infty | SizeVar of SVar.t * int
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val subst : t -> t -> t
end

module Annot :
sig
  type t = Empty | Star | Size of Size.t
  val infty : t
  val hat : t -> t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val sizevar_opt : t -> SVar.t option
  val pr : t -> Pp.t
  val show : t -> string
  val hash : t -> int
end

module Annots :
sig
  type t = Assum | Bare of int | Limit of int | Sized of Size.t array
  val vars : t -> SVars.t
  val length : t -> int
  val pr : t -> Pp.t
  val show : t -> string
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
  val next_annots : bool -> int option -> t -> Annots.t * t
  val pr : t -> Pp.t
end

module SMap :
sig
  type t
  val empty : t
  val add : SVar.t -> Size.t -> t -> t
  val get : SVar.t -> t -> Size.t
  val subst : t -> Size.t -> Size.t
  val pr : t -> Pp.t
end

module Constraints :
sig
  type t
  type 'a constrained = 'a * t
  val empty : unit -> t
  val union : t -> t -> t
  val add : Annot.t -> Annot.t -> t -> t
  val map : SMap.t -> t -> t
  val pr : t -> Pp.t
end

(* N.B. Only [rec_check] should be exposed, but we expose the rest for testing. *)
module RecCheck :
sig
  type g
  val to_graph : Constraints.t -> g
  val of_graph : g -> Constraints.t

  val contains : g -> SVar.t -> SVar.t -> bool
  val sup : g -> SVar.t -> SVars.t
  val sub : g -> SVar.t -> SVars.t
  val find_negative_cycle_vars : g -> SVars.t

  exception RecCheckFailed of Constraints.t * SVars.t * SVars.t

  val downward : g -> SVars.t -> SVars.t
  val upward   : g -> SVars.t -> SVars.t

  val rec_check : SVar.t -> SVars.t -> SVars.t -> Constraints.t -> Constraints.t
  val solve : Constraints.t -> State.t -> State.t * SMap.t
end
