(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)


(** Combinators on monadic computations. *)


(** A minimal definition necessary for the definition to go through. *)
module type Def = sig

  type +'a t
  val return : 'a -> 'a t
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t

  (** The monadic laws must hold:
      - [(x>>=f)>>=g] = [x>>=fun x' -> (f x'>>=g)]
      - [return a >>= f] = [f a]
      - [x>>=return] = [x]  *)

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

end

module type S = sig

  include Def

  module List : ListS with type 'a t := 'a t

end

(** Expands the monadic definition to extra combinators. *)
module Make (M:Def) : S with type +'a t = 'a M.t
