(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module type S = module type of Array

module type ExtS =
sig
  include S
  val compare : ('a -> 'a -> int) -> 'a array -> 'a array -> int
  (** First size comparison, then lexicographic order. *)

  val equal : ('a -> 'a -> bool) -> 'a array -> 'a array -> bool
  (** Lift equality to array type. *)

  val equal_norefl : ('a -> 'a -> bool) -> 'a array -> 'a array -> bool
  (** Like {!equal} but does not assume that equality is reflexive: no
      optimisation is performed if both arrays are physically the
      same. *)

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
  val fold_left4 :
    ('a -> 'b -> 'c -> 'd -> 'e -> 'a) -> 'a -> 'b array -> 'c array -> 'd array -> 'e array -> 'a
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
  [@@ocaml.deprecated "Same as [Smart.map]"]

  val smartfoldmap : ('r -> 'a -> 'r * 'a) -> 'r -> 'a array -> 'r * 'a array
  [@@ocaml.deprecated "Same as [Smart.fold_left_map]"]

  val map2 : ('a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
  (** See also [Smart.map2] *)

  val map2_i : (int -> 'a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
  val map3 :
    ('a -> 'b -> 'c -> 'd) -> 'a array -> 'b array -> 'c array -> 'd array

  val map_left : ('a -> 'b) -> 'a array -> 'b array
  (** As [map] but guaranteed to be left-to-right. *)

  val iter2 : ('a -> 'b -> unit) -> 'a array -> 'b array -> unit
  (** Iter on two arrays. Raise [Invalid_argument "Array.iter2"] if sizes differ. *)

  val iter2_i : (int -> 'a -> 'b -> unit) -> 'a array -> 'b array -> unit
  (** Iter on two arrays. Raise [Invalid_argument "Array.iter2_i"] if sizes differ. *)

  val fold_left_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b array -> 'a * 'c array
  (** [fold_left_map f e_0 [|l_1...l_n|] = e_n,[|k_1...k_n|]]
    where [(e_i,k_i)=f e_{i-1} l_i]; see also [Smart.fold_left_map] *)

  val fold_right_map : ('a -> 'c -> 'b * 'c) -> 'a array -> 'c -> 'b array * 'c
  (** Same, folding on the right *)

  val fold_left2_map : ('a -> 'b -> 'c -> 'a * 'd) -> 'a -> 'b array -> 'c array -> 'a * 'd array
  (** Same with two arrays, folding on the left; see also [Smart.fold_left2_map] *)

  val fold_right2_map : ('a -> 'b -> 'c -> 'd * 'c) -> 'a array -> 'b array -> 'c -> 'd array * 'c
  (** Same with two arrays, folding on the left *)

  val fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b array -> 'a * 'c array
  [@@ocaml.deprecated "Same as [fold_left_map]"]

  val fold_map' : ('a -> 'c -> 'b * 'c) -> 'a array -> 'c -> 'b array * 'c
  [@@ocaml.deprecated "Same as [fold_right_map]"]

  val fold_map2' :
    ('a -> 'b -> 'c -> 'd * 'c) -> 'a array -> 'b array -> 'c -> 'd array * 'c
  [@@ocaml.deprecated "Same as [fold_right2_map]"]

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

  module Smart :
  sig
    val map : ('a -> 'a) -> 'a array -> 'a array
    (** [Smart.map f a] behaves as [map f a] but returns [a] instead of a copy when
        [f x == x] for all [x] in [a]. *)

    val map2 : ('a -> 'b -> 'b) -> 'a array -> 'b array -> 'b array
    (** [Smart.map2 f a b] behaves as [map2 f a b] but returns [a] instead of a copy when
        [f x y == y] for all [x] in [a] and [y] in [b] pointwise. *)

    val fold_left_map : ('a -> 'b -> 'a * 'b) -> 'a -> 'b array -> 'a * 'b array
    (** [Smart.fold_left_mapf a b] behaves as [fold_left_map] but
        returns [b] as second component instead of a copy of [b] when
        the output array is pointwise the same as the input array [b] *)

    val fold_left2_map : ('a -> 'b -> 'c -> 'a * 'c) -> 'a -> 'b array -> 'c array -> 'a * 'c array
    (** [Smart.fold_left2_map f a b c] behaves as [fold_left2_map] but
        returns [c] as second component instead of a copy of [c] when
        the output array is pointwise the same as the input array [c] *)

  end
  (** The functions defined in this module are optimized specializations
      of the main ones, when the returned array is of same type as one of
      the original array. *)

  module Fun1 :
  sig
    val map : ('r -> 'a -> 'b) -> 'r -> 'a array -> 'b array
    (** [Fun1.map f x v = map (f x) v] *)

    val smartmap : ('r -> 'a -> 'a) -> 'r -> 'a array -> 'a array
    [@@ocaml.deprecated "Same as [Fun1.Smart.map]"]

    val iter : ('r -> 'a -> unit) -> 'r -> 'a array -> unit
    (** [Fun1.iter f x v = iter (f x) v] *)

    val iter2 : ('r -> 'a -> 'b -> unit) -> 'r -> 'a array -> 'b array -> unit
    (** [Fun1.iter2 f x v1 v2 = iter (f x) v1 v2] *)

    module Smart :
    sig
      val map : ('r -> 'a -> 'a) -> 'r -> 'a array -> 'a array
      (** [Fun1.Smart.map f x v = Smart.map (f x) v] *)
    end

  end
  (** The functions defined in this module are the same as the main ones, except
      that they are all higher-order, and their function arguments have an
      additional parameter. This allows us to prevent closure creation in critical
      cases. *)

end

include ExtS
