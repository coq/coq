(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


(** Combinators on monadic computations. *)


(** A definition of monads, each of the combinators is used in the
    [Make] functor. *)
module type Def = sig

  type +'a t
  val return : 'a -> 'a t
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
  val (>>) : unit t -> 'a t -> 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t

(** The monadic laws must hold:
    - [(x>>=f)>>=g] = [x>>=fun x' -> (f x'>>=g)]
    - [return a >>= f] = [f a]
    - [x>>=return] = [x]

    As well as the following identities:
    - [x >> y] = [x >>= fun () -> y]
    - [map f x] = [x >>= fun x' -> f x'] *)

end


(** List combinators *)
module type ListS = sig

  type 'a t

  (** [List.map f l] maps [f] on the elements of [l] in left to right
      order. *)
  val map : ('a -> 'b t) -> 'a list -> 'b list t

  (** [List.map f l] maps [f] on the elements of [l] in right to left
      order. *)
  val map_right : ('a -> 'b t) -> 'a list -> 'b list t

  (** Like the regular [List.fold_right]. The monadic effects are
      threaded right to left.

      Note: many monads behave poorly with right-to-left order. For
      instance a failure monad would still have to traverse the
      whole list in order to fail and failure needs to be propagated
      through the rest of the list in binds which are now
      spurious. It is also the worst case for substitution monads
      (aka free monads), exposing the quadratic behaviour.*)
  val fold_right : ('a -> 'b -> 'b t) -> 'a list -> 'b -> 'b t

  (** Like the regular [List.fold_left]. The monadic effects are
      threaded left to right. It is tail-recursive if the [(>>=)]
      operator calls its second argument in a tail position. *)
  val fold_left : ('a -> 'b -> 'a t) -> 'a -> 'b list -> 'a t

  (** Like the regular [List.iter]. The monadic effects are threaded
      left to right. It is tail-recurisve if the [>>] operator calls
      its second argument in a tail position. *)
  val iter : ('a -> unit t) -> 'a list -> unit t

  (** Like the regular {!CList.map_filter}. The monadic effects are
      threaded left to right. *)
  val map_filter : ('a -> 'b option t) -> 'a list -> 'b list t


  (** {6 Two-list iterators} *)

  (** [fold_left2 r f s l1 l2] behaves like {!fold_left} but acts
      simultaneously on two lists. Runs [r] (presumably an
      exception-raising computation) if both lists do not have the
      same length. *)
  val fold_left2 : 'a t ->
    ('a -> 'b -> 'c -> 'a t) -> 'a -> 'b list -> 'c list -> 'a t

end

module type S = sig

  include Def

  module List : ListS with type 'a t := 'a t

end

(** Expands the monadic definition to extra combinators. *)
module Make (M:Def) : S with type +'a t = 'a M.t
