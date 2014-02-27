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


module type S = sig

  include Def

  (** List combinators *)
  module List : sig

    (** [map f l] applies the monadic effect left to right. *)
    val map : ('a -> 'b t) -> 'a list -> 'b list t

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

  end

end
