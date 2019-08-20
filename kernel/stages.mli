(**
  A primer on the structure of sized types.

  Every (co)inductive type comes with an annotation, indicating whether it
  has a size, or whether it is in some special position.
    e.g. List^α1 Nat^α2 is the annotated type of a list of nats

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
    * Glob annotations: These appear only in the types of global declarations,
      similar to star annotations, and help indicate functions that preserve
      the size of the types of their arguments.
        e.g. Definition minus : Natⁱ -> Natⁱ
      For instance, in an implementation of division that uses minus,
      type-checking will only succeed if minus preserves size.
    * Stage annotations: These contain size information.

  There are two types of stages [Stage]:
    * Infty: A (co)inductive type with infinite size is said to be a "full"
      type, and the same type with any other size is a sub-(or super-)type
      of the full inductive (or coinductive) type.
        e.g. ∀α Nat^α ≤ Nat^∞
    * StageVar: A stage containing a stage variable and a successor value.
      Normally stages are ordinals counting the constructor depth of a type,
      but in this system (CIC^) we merely need a stage variable to be picked
      out of some set of enumerables, and add on the number of hats it has.
        e.g. ∀s s ⊑ ŝ, which we also write as (s+1)

  Although stage variables can be any sort of enumerable, for convenience,
  we use the zero-inclusive naturals. Sets of stage variables [SVars] are
  therefore simply IntSets.

  We use [State] to keep track of a few things:
    * The next stage variable that we can use;
    * The set of all stage variables used so far; and
    * The set of stage variables corresponding to position annotations.
  The latter is important during type-checking of (co)fixpoints.

  Finally, we use [Constraints] to keep track of the stage constraints induced
  by subtyping relations.
    e.g. List^α1 Nat ≤ List^α2 ⟹ α1 ⊑ α2
*)

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
  val pr : t -> Pp.t
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
  val compare : t -> t -> int
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
  val next_annots : int option -> t -> Annot.t list option * t
  val pr : t -> Pp.t
end

module Constraints :
sig
  type t
  type 'a constrained = 'a * t
  val empty : unit -> t
  val union : t -> t -> t
  val union_list : t list -> t
  val contains : t -> SVars.var -> SVars.var -> bool
  val add : Annot.t -> Annot.t -> t -> t
  val sup : t -> SVars.var -> SVars.t
  val sub : t -> SVars.var -> SVars.t
  val bellman_ford : t -> SVars.t
  val pr : t -> Pp.t
end

exception RecCheckFailed of Constraints.t * SVars.t * SVars.t

val downward : Constraints.t -> SVars.t -> SVars.t
val upward   : Constraints.t -> SVars.t -> SVars.t

val rec_check : SVars.var -> SVars.t -> SVars.t -> Constraints.t -> Constraints.t

(* N.B. We expose the following ONLY for testing in Stages_test:
  * SVars.is_empty
  * Constraints.contains
  * Constraints.sup
  * Constraints.sub
  * bellman_ford
  * downward
  * upward
*)
