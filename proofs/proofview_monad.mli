(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file defines the low-level monadic operations used by the
    tactic monad. The monad is divided into two layers: a non-logical
    layer which consists in operations which will not (or cannot) be
    backtracked in case of failure (input/output or persistent state)
    and a logical layer which handles backtracking, proof
    manipulation, and any other effect which needs to backtrack. *)

(** {6 States of the logical monad} *)

type proofview = { solution : Evd.evar_map; comb : Goal.goal list }

(** Read/write *)
type logicalState = proofview

(** Read only *)
type logicalEnvironment = Environ.env

(** Write only. Must be a monoid.

    Status (safe/unsafe) * ( shelved goals * given up ). *)
type logicalMessageType = bool * ( Goal.goal list * Goal.goal list )


(** {6 Exceptions} *)


(** To help distinguish between exceptions raised by the IO monad from
    the one used natively by Coq, the former are wrapped in
    [Exception].  It is only used internally so that [catch] blocks of
    the IO monad would only catch exceptions raised by the [raise]
    function of the IO monad, and not for instance, by system
    interrupts. Also used in [Proofview] to avoid capturing exception
    from the IO monad ([Proofview] catches errors in its compatibility
    layer, and when lifting goal-level expressions). *)
exception Exception of exn
(** This exception is used to signal abortion in [timeout] functions. *)
exception Timeout
(** This exception is used by the tactics to signal failure by lack of
    successes, rather than some other exceptions (like system
    interrupts). *)
exception TacticFailure of exn


(** {6 Non-logical layer} *)

(** The non-logical monad is a simple [unit -> 'a] (i/o) monad. The
    operations are simple wrappers around corresponding usual
    operations and require little documentation. *)
module NonLogical : sig

  type +'a t
  type 'a ref

  val ret : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val ignore : 'a t -> unit t
  val seq : unit t -> 'a t -> 'a t

  val ref : 'a -> 'a ref t
  (** [Pervasives.(:=)] *)
  val set : 'a ref -> 'a -> unit t
  (** [Pervasives.(!)] *)
  val get : 'a ref -> 'a t

  val read_line : string t
  val print_char : char -> unit t
  (** {!Pp.pp}. The buffer is also flushed. *)
  val print : Pp.std_ppcmds -> unit t

  (** [Pervasives.raise]. Except that exceptions are wrapped with
      {!Exception}. *)
  val raise : exn -> 'a t
  (** [try ... with ...] but restricted to {!Exception}. *)
  val catch : 'a t -> (exn -> 'a t) -> 'a t
  val timeout : int -> 'a t -> 'a t

  (** Construct a monadified side-effect. Exceptions raised by the argument are
      wrapped with {!Exception}. *)
  val make : (unit -> 'a) -> 'a t

  (** [run] performs effects. *)
  val run : 'a t -> 'a

end


(** {6 Logical layer} *)

(** The logical monad is a backtracking monad on top of which is
    layered a state monad (which is used to implement all of read/write,
    read only, and write only effects). The state monad being layered on
    top of the backtracking monad makes it so that the state is
    backtracked on failure.

    Backtracking differs from regular exception in that, writing (+)
    for exception catching and (>>=) for bind, we require the
    following extra distributivity laws:

    x+(y+z) = (x+y)+z

    zero+x = x

    x+zero = x

    (x+y)>>=k = (x>>=k)+(y>>=k) *)

(** A view type for the logical monad, which is a form of list, hence
    we can decompose it with as a list. *)
type ('a, 'b) list_view =
| Nil of exn
| Cons of 'a * 'b

module Logical : sig

  type +'a t

  val ret : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val ignore : 'a t -> unit t
  val seq : unit t -> 'a t -> 'a t

  val set : logicalState -> unit t
  val get : logicalState t
  val modify : (logicalState -> logicalState) -> unit t
  val put : logicalMessageType -> unit t
  val current : logicalEnvironment t
  val update : logicalEnvironment -> unit t

  val zero : exn -> 'a t
  val plus : 'a t -> (exn -> 'a t) -> 'a t
  val split : 'a t -> (('a,(exn->'a t)) list_view) t
  val once : 'a t -> 'a t
  val break : (exn -> bool) -> 'a t -> 'a t

  val lift : 'a NonLogical.t -> 'a t

  val run : 'a t -> logicalEnvironment -> logicalState -> (('a*logicalState)*logicalMessageType) NonLogical.t
end
