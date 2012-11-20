(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** FIXME: From OCaml 3.12 onwards, that would only be a [module type of] *)

(** Module type [S] is the one from OCaml Stdlib. *)
module type S =
sig
  val length : 'a list -> int
  val hd : 'a list -> 'a
  val tl : 'a list -> 'a list
  val nth : 'a list -> int -> 'a
  val rev : 'a list -> 'a list
  val append : 'a list -> 'a list -> 'a list
  val rev_append : 'a list -> 'a list -> 'a list
  val concat : 'a list list -> 'a list
  val flatten : 'a list list -> 'a list
  val iter : ('a -> unit) -> 'a list -> unit
  val map : ('a -> 'b) -> 'a list -> 'b list
  val rev_map : ('a -> 'b) -> 'a list -> 'b list
  val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
  val fold_right : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val iter2 : ('a -> 'b -> unit) -> 'a list -> 'b list -> unit
  val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val rev_map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
  val fold_right2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
  val for_all : ('a -> bool) -> 'a list -> bool
  val exists : ('a -> bool) -> 'a list -> bool
  val for_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val exists2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val mem : 'a -> 'a list -> bool
  val memq : 'a -> 'a list -> bool
  val find : ('a -> bool) -> 'a list -> 'a
  val filter : ('a -> bool) -> 'a list -> 'a list
  val find_all : ('a -> bool) -> 'a list -> 'a list
  val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
  val assoc : 'a -> ('a * 'b) list -> 'b
  val assq : 'a -> ('a * 'b) list -> 'b
  val mem_assoc : 'a -> ('a * 'b) list -> bool
  val mem_assq : 'a -> ('a * 'b) list -> bool
  val remove_assoc : 'a -> ('a * 'b) list -> ('a * 'b) list
  val remove_assq : 'a -> ('a * 'b) list -> ('a * 'b) list
  val split : ('a * 'b) list -> 'a list * 'b list
  val combine : 'a list -> 'b list -> ('a * 'b) list
  val sort : ('a -> 'a -> int) -> 'a list -> 'a list
  val stable_sort : ('a -> 'a -> int) -> 'a list -> 'a list
  val fast_sort : ('a -> 'a -> int) -> 'a list -> 'a list
  val merge : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list
end

module type ExtS =
sig
  include S
  val compare : ('a -> 'a -> int) -> 'a list -> 'a list -> int
  (** Lexicographic order on lists. *)

  val equal : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
  (** Lifts equality to list type. *)

  val add_set : 'a -> 'a list -> 'a list
  (** [add_set x l] adds [x] in [l] if it is not already there, or returns [l]
      otherwise. *)

  val eq_set : 'a list -> 'a list -> bool
  (** Test equality up to permutation. *)

  val intersect : 'a list -> 'a list -> 'a list
  val union : 'a list -> 'a list -> 'a list
  val unionq : 'a list -> 'a list -> 'a list
  val subtract : 'a list -> 'a list -> 'a list
  val subtractq : 'a list -> 'a list -> 'a list

  val tabulate : (int -> 'a) -> int -> 'a list
  (** [tabulate f n] builds [[f 0; ...; f (n-1)]] *)

  val interval : int -> int -> int list
  (** [interval i j] creates the list [[i; i + 1; ...; j]], or [[]] when 
      [j <= i]. *)

  val make : int -> 'a -> 'a list
  (** [make n x] returns a list made of [n] times [x]. Raise
      [Invalid_argument "List.make"] if [n] is negative. *)

  val assign : 'a list -> int -> 'a -> 'a list
  (** [assign l i x] set the [i]-th element of [l] to [x], starting from [0]. *)

  val distinct : 'a list -> bool
  (** Return [true] if all elements of the list are distinct. *)

  val duplicates : 'a list -> 'a list
  (** Return the list of unique elements which appear at least twice. Elements
      are kept in the order of their first appearance. *)

  val filter2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list * 'b list
  val map_filter : ('a -> 'b option) -> 'a list -> 'b list
  val map_filter_i : (int -> 'a -> 'b option) -> 'a list -> 'b list

  val filter_with : bool list -> 'a list -> 'a list
  (** [filter_with b a] selects elements of [a] whose corresponding element in
      [b] is [true]. Raise [Invalid_argument _] when sizes differ. *)

  val smartmap : ('a -> 'a) -> 'a list -> 'a list
  (** [smartmap f [a1...an] = List.map f [a1...an]] but if for all i
    [f ai == ai], then [smartmap f l == l] *)

  val map_left : ('a -> 'b) -> 'a list -> 'b list
  (** As [map] but ensures the left-to-right order of evaluation. *)

  val map_i : (int -> 'a -> 'b) -> int -> 'a list -> 'b list
  (** As [map] but with the index, which starts from [0]. *)

  val map2_i :
    (int -> 'a -> 'b -> 'c) -> int -> 'a list -> 'b list -> 'c list
  val map3 :
    ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list
  val map4 : ('a -> 'b -> 'c -> 'd -> 'e) -> 'a list -> 'b list -> 'c list ->
    'd list -> 'e list
  val filteri : (int -> 'a -> bool) -> 'a list -> 'a list

  val smartfilter : ('a -> bool) -> 'a list -> 'a list
  (** [smartfilter f [a1...an] = List.filter f [a1...an]] but if for all i
    [f ai = true], then [smartfilter f l == l] *)

  val index : 'a -> 'a list -> int
  (** [index] returns the 1st index of an element in a list (counting from 1). *)

  val index_f : ('a -> 'a -> bool) -> 'a -> 'a list -> int

  val unique_index : 'a -> 'a list -> int
  (** [unique_index x l] returns [Not_found] if [x] doesn't occur exactly once. *)

  val index0 : 'a -> 'a list -> int
  (** [index0] behaves as [index] except that it starts counting at 0. *)

  val index0_f : ('a -> 'a -> bool) -> 'a -> 'a list -> int

  val iteri :  (int -> 'a -> unit) -> 'a list -> unit
  (** As [iter] but with the index argument (starting from 0). *)

  val fold_right_i :  (int -> 'a -> 'b -> 'b) -> int -> 'a list -> 'b -> 'b
  val fold_left_i :  (int -> 'a -> 'b -> 'a) -> int -> 'a -> 'b list -> 'a
  val fold_right_and_left :
      ('a -> 'b -> 'b list -> 'a) -> 'b list -> 'a -> 'a
  val fold_left3 : ('a -> 'b -> 'c -> 'd -> 'a) -> 'a -> 'b list -> 'c list -> 'd list -> 'a
  val for_all_i : (int -> 'a -> bool) -> int -> 'a list -> bool
  val except : 'a -> 'a list -> 'a list
  val remove : 'a -> 'a list -> 'a list
  val remove_first : 'a -> 'a list -> 'a list
  val remove_assoc_in_triple : 'a -> ('a * 'b * 'c) list -> ('a * 'b * 'c) list
  val assoc_snd_in_triple : 'a -> ('a * 'b * 'c) list -> 'b
  val for_all2eq : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val sep_last : 'a list -> 'a * 'a list

  val find_map : ('a -> 'b option) -> 'a list -> 'b
  (** Returns the first element that is mapped to [Some _]. Raise [Not_found] if
      there is none. *)

  val uniquize : 'a list -> 'a list
  (** Return the list of elements without duplicates. *)

  val merge_uniq : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list
  (** Merge two sorted lists and preserves the uniqueness property. *)

  val subset : 'a list -> 'a list -> bool
  val chop : int -> 'a list -> 'a list * 'a list
  val split_when : ('a -> bool) -> 'a list -> 'a list * 'a list
  val split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
  val firstn : int -> 'a list -> 'a list
  val last : 'a list -> 'a
  val lastn : int -> 'a list -> 'a list
  val skipn : int -> 'a list -> 'a list
  val skipn_at_least : int -> 'a list -> 'a list

  val addn : int -> 'a -> 'a list -> 'a list
  (** [addn n x l] adds [n] times [x] on the left of [l]. *)

  val prefix_of : 'a list -> 'a list -> bool
  (** [prefix_of l1 l2] returns [true] if [l1] is a prefix of [l2], [false]
      otherwise. *)

  val drop_prefix : 'a list -> 'a list -> 'a list
  (** [drop_prefix p l] returns [t] if [l=p++t] else return [l]. *)

  val drop_last : 'a list -> 'a list

  val map_append : ('a -> 'b list) -> 'a list -> 'b list
  (** [map_append f [x1; ...; xn]] returns [(f x1)@(f x2)@...@(f xn)]. *)

  val map_append2 : ('a -> 'b -> 'c list) -> 'a list -> 'b list -> 'c list
  (** As [map_append]. Raises [Invalid_argument _] if the two lists don't have 
      the same length. *)

  val share_tails : 'a list -> 'a list -> 'a list * 'a list * 'a list

  val fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
  (** [fold_map f e_0 [l_1...l_n] = e_n,[k_1...k_n]]
    where [(e_i,k_i)=f e_{i-1} l_i] *)

  val fold_map' : ('b -> 'a -> 'c * 'a) -> 'b list -> 'a -> 'c list * 'a
  val map_assoc : ('a -> 'b) -> ('c * 'a) list -> ('c * 'b) list
  val assoc_f : ('a -> 'a -> bool) -> 'a -> ('a * 'b) list -> 'b

  val cartesian : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  (** A generic cartesian product: for any operator (**),
    [cartesian (**) [x1;x2] [y1;y2] = [x1**y1; x1**y2; x2**y1; x2**y1]],
    and so on if there are more elements in the lists. *)

  val cartesians : ('a -> 'b -> 'b) -> 'b -> 'a list list -> 'b list
  (** [cartesians] is an n-ary cartesian product: it iterates
    [cartesian] over a list of lists.  *)

  val combinations : 'a list list -> 'a list list
  (** combinations [[a;b];[c;d]] returns [[a;c];[a;d];[b;c];[b;d]] *)

  val combine3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list

  val cartesians_filter :
    ('a -> 'b -> 'b option) -> 'b -> 'a list list -> 'b list
  (** Keep only those products that do not return None *)

  val factorize_left : ('a * 'b) list -> ('a * 'b list) list
end

include ExtS
