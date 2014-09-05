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

module type ListS = sig
  type 'a t
  val map : ('a -> 'b t) -> 'a list -> 'b list t
  val map_right : ('a -> 'b t) -> 'a list -> 'b list t
  val fold_right : ('a -> 'b -> 'b t) -> 'a list -> 'b -> 'b t
  val fold_left : ('a -> 'b -> 'a t) -> 'a -> 'b list -> 'a t
end

module type S = sig

  include Def

  (** List combinators *)
  module List : sig

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

end


module Make (M:Def) : S with type +'a t = 'a M.t = struct

  include M

  module List = struct

    let rec map f = function
      | [] -> return []
      | a::l ->
          f a >>= fun a' ->
          map f l >>= fun l' ->
          return (a'::l')

    let rec map_right f = function
      | [] -> return []
      | a::l ->
          map f l >>= fun l' ->
          f a >>= fun a' ->
          return (a'::l')

    let rec fold_right f l x =
      match l with
      | [] -> return x
      | a::l ->
          fold_right f l x >>= fun acc ->
          f a acc

    let rec fold_left f x = function
      | [] -> return x
      | a::l ->
          f x a >>= fun x' ->
          fold_left f x' l
  end

end
