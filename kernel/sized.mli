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
    * Glob annotations: These appear only in the types of global declarations,
      similar to star annotations, and help indicate functions that preserve
      the size of the types of their arguments.
        e.g. Definition minus : Natⁱ -> Natⁱ
      For instance, in an implementation of division that uses minus,
      type-checking will only succeed if minus preserves size.
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

module SVars :
sig
  type t
  type var = int
  val empty : t
  val is_empty : t -> bool
  val add : var -> t -> t
  val mem : var -> t -> bool
  val of_list : var list -> t
  val union : t -> t -> t
  val union_list : t list -> t
  val inter : t -> t -> t
  val diff : t -> t -> t
  val fold : (var -> 'a -> 'a) -> t -> 'a -> 'a
  val pr : t -> Pp.t
end

module Size :
sig
  type t = Infty | SizeVar of SVars.var * int
  val compare : t -> t -> int
end

module Annot :
sig
  type t = Empty | Star | Glob | Size of Size.t
  type ts = t list option
  val infty : t
  val hat : t -> t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val sizevar_opt : t -> SVars.var option
  val pr : t -> Pp.t
  val show : t -> string
  val hash : t -> int
  val hashAns : ts -> int
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
  val add : Annot.t -> Annot.t -> t -> t
  val pr : t -> Pp.t
end

(* N.B. Only [rec_check] should be exposed, but we expose the rest for testing. *)
module RecCheck :
sig
  type g
  val to_graph : Constraints.t -> g
  val of_graph : g -> Constraints.t

  val contains : g -> SVars.var -> SVars.var -> bool
  val sup : g -> SVars.var -> SVars.t
  val sub : g -> SVars.var -> SVars.t
  val bellman_ford : g -> SVars.t

  exception RecCheckFailed of Constraints.t * SVars.t * SVars.t

  val downward : g -> SVars.t -> SVars.t
  val upward   : g -> SVars.t -> SVars.t

  val rec_check : SVars.var -> SVars.t -> SVars.t -> Constraints.t -> Constraints.t
end
