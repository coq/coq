(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

type 'a cmp = 'a -> 'a -> int
type 'a eq = 'a -> 'a -> bool

(** Module type [S] is the one from OCaml Stdlib. *)
module type S = module type of List

module type ExtS =
sig
  include S

  val compare : 'a cmp -> 'a list cmp
  (** Lexicographic order on lists. *)

  val equal : 'a eq -> 'a list eq
  (** Lifts equality to list type. *)

  val is_empty : 'a list -> bool
  (** Checks whether a list is empty *)

  val init : int -> (int -> 'a) -> 'a list
  (** [init n f] constructs the list [f 0; ... ; f (n - 1)]. *)

  val mem_f : 'a eq -> 'a -> 'a list -> bool
  (* Same as [List.mem], for some specific equality *)

  val add_set : 'a eq -> 'a -> 'a list -> 'a list
  (** [add_set x l] adds [x] in [l] if it is not already there, or returns [l]
      otherwise. *)

  val eq_set : 'a eq -> 'a list eq
  (** Test equality up to permutation (but considering multiple occurrences) *)

  val intersect : 'a eq -> 'a list -> 'a list -> 'a list
  val union : 'a eq -> 'a list -> 'a list -> 'a list
  val unionq : 'a list -> 'a list -> 'a list
  val subtract : 'a eq -> 'a list -> 'a list -> 'a list
  val subtractq : 'a list -> 'a list -> 'a list

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

  val distinct_f : 'a cmp -> 'a list -> bool

  val duplicates : 'a eq -> 'a list -> 'a list
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

  val index : 'a eq -> 'a -> 'a list -> int
  (** [index] returns the 1st index of an element in a list (counting from 1). *)

  val index0 : 'a eq -> 'a -> 'a list -> int
  (** [index0] behaves as [index] except that it starts counting at 0. *)

  val iteri :  (int -> 'a -> unit) -> 'a list -> unit
  (** As [iter] but with the index argument (starting from 0). *)

  val fold_left_until : ('c -> 'a -> 'c CSig.until) -> 'c -> 'a list -> 'c
  (** acts like [fold_left f acc s] while [f] returns
      [Cont acc']; it stops returning [c] as soon as [f] returns [Stop c]. *)

  val fold_right_i :  (int -> 'a -> 'b -> 'b) -> int -> 'a list -> 'b -> 'b
  val fold_left_i :  (int -> 'a -> 'b -> 'a) -> int -> 'a -> 'b list -> 'a
  val fold_right_and_left :
      ('a -> 'b -> 'b list -> 'a) -> 'b list -> 'a -> 'a
  val fold_left3 : ('a -> 'b -> 'c -> 'd -> 'a) -> 'a -> 'b list -> 'c list -> 'd list -> 'a
  val for_all_i : (int -> 'a -> bool) -> int -> 'a list -> bool
  val except : 'a eq -> 'a -> 'a list -> 'a list
  val remove : 'a eq -> 'a -> 'a list -> 'a list

  val remove_first : ('a -> bool) -> 'a list -> 'a list
  (** Remove the first element satisfying a predicate, or raise [Not_found] *)

  val insert : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list
  (** Insert at the (first) position so that if the list is ordered wrt to the
      total order given as argument, the order is preserved *)

  val for_all2eq : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val sep_last : 'a list -> 'a * 'a list

  val find_map : ('a -> 'b option) -> 'a list -> 'b
  (** Returns the first element that is mapped to [Some _]. Raise [Not_found] if
      there is none. *)

  val uniquize : 'a list -> 'a list
  (** Return the list of elements without duplicates.
      This is the list unchanged if there was none. *)

  val sort_uniquize : 'a cmp -> 'a list -> 'a list
  (** Return a sorted and de-duplicated version of a list,
      according to some comparison function. *)

  val merge_uniq : 'a cmp -> 'a list -> 'a list -> 'a list
  (** Merge two sorted lists and preserves the uniqueness property. *)

  val subset : 'a list -> 'a list -> bool

  val chop : int -> 'a list -> 'a list * 'a list
  (** [chop i l] splits [l] into two lists [(l1,l2)] such that
      [l1++l2=l] and [l1] has length [i].  It raises [Failure] when [i]
      is negative or greater than the length of [l] *)

  exception IndexOutOfRange
  val goto: int -> 'a list -> 'a list * 'a list
  (** [goto i l] splits [l] into two lists [(l1,l2)] such that
      [(List.rev l1)++l2=l] and [l1] has length [i].  It raises
      [IndexOutOfRange] when [i] is negative or greater than the
      length of [l]. *)


  val split_when : ('a -> bool) -> 'a list -> 'a list * 'a list
  val split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
  val firstn : int -> 'a list -> 'a list
  val last : 'a list -> 'a
  val lastn : int -> 'a list -> 'a list
  val skipn : int -> 'a list -> 'a list
  val skipn_at_least : int -> 'a list -> 'a list

  val addn : int -> 'a -> 'a list -> 'a list
  (** [addn n x l] adds [n] times [x] on the left of [l]. *)

  val prefix_of : 'a eq -> 'a list -> 'a list -> bool
  (** [prefix_of l1 l2] returns [true] if [l1] is a prefix of [l2], [false]
      otherwise. *)

  val drop_prefix : 'a eq -> 'a list -> 'a list -> 'a list
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
  val assoc_f : 'a eq -> 'a -> ('a * 'b) list -> 'b
  val remove_assoc_f : 'a eq -> 'a -> ('a * 'b) list -> ('a * 'b) list
  val mem_assoc_f : 'a eq -> 'a -> ('a * 'b) list -> bool

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

  val factorize_left : 'a eq -> ('a * 'b) list -> ('a * 'b list) list

  module type MonoS = sig
    type elt
    val equal : elt list -> elt list -> bool
    val mem : elt -> elt list -> bool
    val assoc : elt -> (elt * 'a) list -> 'a
    val mem_assoc : elt -> (elt * 'a) list -> bool
    val remove_assoc : elt -> (elt * 'a) list -> (elt * 'a) list
    val mem_assoc_sym : elt -> ('a * elt) list -> bool
  end
end

include ExtS
