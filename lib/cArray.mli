(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

module type S = module type of Array

module type ExtS =
sig
  include S
  val compare : ('a -> 'a -> int) -> 'a array -> 'a array -> int
  (** First size comparison, then lexicographic order. *)

  val equal : ('a -> 'a -> bool) -> 'a array -> 'a array -> bool
  (** Lift equality to array type. *)

  val is_empty : 'a array -> bool
  (** True whenever the array is empty. *)

  val exists : ('a -> bool) -> 'a array -> bool
  (** As [List.exists] but on arrays. *)

  val exists2 : ('a -> 'b -> bool) -> 'a array -> 'b array -> bool

  val for_all : ('a -> bool) -> 'a array -> bool
  val for_all2 : ('a -> 'b -> bool) -> 'a array -> 'b array -> bool
  val for_all3 : ('a -> 'b -> 'c -> bool) ->
    'a array -> 'b array -> 'c array -> bool
  val for_all4 : ('a -> 'b -> 'c -> 'd -> bool) ->
    'a array -> 'b array -> 'c array -> 'd array -> bool
  val for_all_i : (int -> 'a -> bool) -> int -> 'a array -> bool

  val findi : (int -> 'a -> bool) -> 'a array -> int option

  val hd : 'a array -> 'a
  (** First element of an array, or [Failure "Array.hd"] if empty. *)

  val tl : 'a array -> 'a array
  (** Remaining part of [hd], or [Failure "Array.tl"] if empty. *)

  val last : 'a array -> 'a
  (** Last element of an array, or [Failure "Array.last"] if empty. *)

  val cons : 'a -> 'a array -> 'a array
  (** Append an element on the left. *)

  val rev : 'a array -> unit
  (** In place reversal. *)

  val fold_right_i :
    (int -> 'b -> 'a -> 'a) -> 'b array -> 'a -> 'a
  val fold_left_i : (int -> 'a -> 'b -> 'a) -> 'a -> 'b array -> 'a
  val fold_right2 :
    ('a -> 'b -> 'c -> 'c) -> 'a array -> 'b array -> 'c -> 'c
  val fold_left2 :
    ('a -> 'b -> 'c -> 'a) -> 'a -> 'b array -> 'c array -> 'a
  val fold_left3 :
    ('a -> 'b -> 'c -> 'd -> 'a) -> 'a -> 'b array -> 'c array -> 'd array -> 'a
  val fold_left2_i :
    (int -> 'a -> 'b -> 'c -> 'a) -> 'a -> 'b array -> 'c array -> 'a
  val fold_left_from : int -> ('a -> 'b -> 'a) -> 'a -> 'b array -> 'a

  val map_to_list : ('a -> 'b) -> 'a array -> 'b list
  (** Composition of [map] and [to_list]. *)

  val map_of_list : ('a -> 'b) -> 'a list -> 'b array
  (** Composition of [map] and [of_list]. *)

  val chop : int -> 'a array -> 'a array * 'a array
  (** [chop i a] returns [(a1, a2)] s.t. [a = a1 + a2] and [length a1 = n].
      Raise [Failure "Array.chop"] if [i] is not a valid index. *)

  val smartmap : ('a -> 'a) -> 'a array -> 'a array
  (** [smartmap f a] behaves as [map f a] but returns [a] instead of a copy when
      [f x == x] for all [x] in [a]. *)

  val smartfoldmap : ('r -> 'a -> 'r * 'a) -> 'r -> 'a array -> 'r * 'a array
  (** Same as [smartmap] but threads an additional state left-to-right. *)

  val map2 : ('a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
  val map2_i : (int -> 'a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
  val map3 :
    ('a -> 'b -> 'c -> 'd) -> 'a array -> 'b array -> 'c array -> 'd array

  val map_left : ('a -> 'b) -> 'a array -> 'b array
  (** As [map] but guaranteed to be left-to-right. *)

  val iter2 : ('a -> 'b -> unit) -> 'a array -> 'b array -> unit
  (** Iter on two arrays. Raise [Invalid_argument "Array.iter2"] if sizes differ. *)

  val fold_map' : ('a -> 'c -> 'b * 'c) -> 'a array -> 'c -> 'b array * 'c
  val fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b array -> 'a * 'c array
  val fold_map2' :
    ('a -> 'b -> 'c -> 'd * 'c) -> 'a array -> 'b array -> 'c -> 'd array * 'c

  val distinct : 'a array -> bool
  (** Return [true] if every element of the array is unique (for default 
      equality). *)

  val rev_of_list : 'a list -> 'a array
  (** [rev_of_list l] is equivalent to [Array.of_list (List.rev l)]. *)

  val rev_to_list : 'a array -> 'a list
  (** [rev_to_list a] is equivalent to [List.rev (List.of_array a)]. *)

  val filter_with : bool list -> 'a array -> 'a array
  (** [filter_with b a] selects elements of [a] whose corresponding element in
      [b] is [true].  Raise [Invalid_argument _] when sizes differ. *)

end

include ExtS

module Fun1 :
sig
  val map : ('r -> 'a -> 'b) -> 'r -> 'a array -> 'b array
  (** [Fun1.map f x v = map (f x) v] *)

  val smartmap : ('r -> 'a -> 'a) -> 'r -> 'a array -> 'a array
  (** [Fun1.smartmap f x v = smartmap (f x) v] *)

  val iter : ('r -> 'a -> unit) -> 'r -> 'a array -> unit
  (** [Fun1.iter f x v = iter (f x) v] *)

end
(** The functions defined in this module are the same as the main ones, except
    that they are all higher-order, and their function arguments have an
    additional parameter. This allows us to prevent closure creation in critical
    cases. *)
