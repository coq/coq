(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type 'a cmp = 'a -> 'a -> int
type 'a eq = 'a -> 'a -> bool

(** Module type [S] is the one from OCaml Stdlib. *)
module type S = module type of List

module type ExtS =
sig
  include S

  (** {6 Equality, testing} *)

  val compare : 'a cmp -> 'a list cmp
  (** Lexicographic order on lists. *)

  val equal : 'a eq -> 'a list eq
  (** Lift equality to list type. *)

  val is_empty : 'a list -> bool
  (** Check whether a list is empty *)

  val mem_f : 'a eq -> 'a -> 'a list -> bool
  (** Same as [List.mem], for some specific equality *)

  val for_all_i : (int -> 'a -> bool) -> int -> 'a list -> bool
  (** Same as [List.for_all] but with an index *)

  val for_all2eq : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  (** Same as [List.for_all2] but returning [false] when of different length *)

  val prefix_of : 'a eq -> 'a list eq
  (** [prefix_of eq l1 l2] returns [true] if [l1] is a prefix of [l2], [false]
      otherwise. It uses [eq] to compare elements *)

  (** {6 Creating lists} *)

  val interval : int -> int -> int list
  (** [interval i j] creates the list [[i; i + 1; ...; j]], or [[]] when 
      [j <= i]. *)

  val make : int -> 'a -> 'a list
  (** [make n x] returns a list made of [n] times [x]. Raise
      [Invalid_argument _] if [n] is negative. *)

  val addn : int -> 'a -> 'a list -> 'a list
  (** [addn n x l] adds [n] times [x] on the left of [l]. *)

  val init : int -> (int -> 'a) -> 'a list
  (** [init n f] constructs the list [f 0; ... ; f (n - 1)]. Raise
      [Invalid_argument _] if [n] is negative *)

  val append : 'a list -> 'a list -> 'a list
  (** Like OCaml's [List.append] but tail-recursive. *)

  val concat : 'a list list -> 'a list
  (** Like OCaml's [List.concat] but tail-recursive. *)

  val flatten : 'a list list -> 'a list
  (** Synonymous of [concat] *)

  (** {6 Lists as arrays} *)

  val assign : 'a list -> int -> 'a -> 'a list
  (** [assign l i x] sets the [i]-th element of [l] to [x], starting
      from [0]. Raise [Failure _] if [i] is out of range. *)

  (** {6 Filtering} *)

  val filter : ('a -> bool) -> 'a list -> 'a list
  (** Like OCaml [List.filter] but tail-recursive and physically returns
      the original list if the predicate holds for all elements. *)

  val filter2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list * 'b list
  (** Like [List.filter] but with 2 arguments, raise [Invalid_argument _]
      if the lists are not of same length. *)

  val filteri : (int -> 'a -> bool) -> 'a list -> 'a list
  (** Like [List.filter] but with an index starting from [0] *)

  val filter_with : bool list -> 'a list -> 'a list
  (** [filter_with bl l] selects elements of [l] whose corresponding element in
      [bl] is [true]. Raise [Invalid_argument _] if sizes differ. *)

  val smartfilter : ('a -> bool) -> 'a list -> 'a list
  [@@ocaml.deprecated "Same as [filter]"]

  val map_filter : ('a -> 'b option) -> 'a list -> 'b list
  (** Like [map] but keeping only non-[None] elements *)

  val map_filter_i : (int -> 'a -> 'b option) -> 'a list -> 'b list
  (** Like [map_filter] but with an index starting from [0] *)

  val partitioni : (int -> 'a -> bool) -> 'a list -> 'a list * 'a list
  (** Like [List.partition] but with an index starting from [0] *)

  (** {6 Applying functorially} *)

  val map : ('a -> 'b) -> 'a list -> 'b list
  (** Like OCaml [List.map] but tail-recursive *)

  val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  (** Like OCaml [List.map2] but tail-recursive *)

  val smartmap : ('a -> 'a) -> 'a list -> 'a list
  [@@ocaml.deprecated "Same as [Smart.map]"]

  val map_left : ('a -> 'b) -> 'a list -> 'b list
  (** As [map] but ensures the left-to-right order of evaluation. *)

  val map_i : (int -> 'a -> 'b) -> int -> 'a list -> 'b list
  (** Like OCaml [List.mapi] but tail-recursive. Alternatively, like
      [map] but with an index *)

  val map2_i :
    (int -> 'a -> 'b -> 'c) -> int -> 'a list -> 'b list -> 'c list
  (** Like [map2] but with an index *)

  val map3 :
    ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list
  (** Like [map] but for 3 lists. *)

  val map4 : ('a -> 'b -> 'c -> 'd -> 'e) -> 'a list -> 'b list -> 'c list ->
    'd list -> 'e list
  (** Like [map] but for 4 lists. *)

  val map_of_array : ('a -> 'b) -> 'a array -> 'b list
  (** [map_of_array f a] behaves as [List.map f (Array.to_list a)] *)

  val map_append : ('a -> 'b list) -> 'a list -> 'b list
  (** [map_append f [x1; ...; xn]] returns [f x1 @ ... @ f xn]. *)

  val map_append2 : ('a -> 'b -> 'c list) -> 'a list -> 'b list -> 'c list
  (** Like [map_append] but for two lists; raises [Invalid_argument _]
      if the two lists do not have the same length. *)

  val extend : bool list -> 'a -> 'a list -> 'a list
  (** [extend l a [a1..an]] assumes that the number of [true] in [l] is [n];
    it extends [a1..an] by inserting [a] at the position of [false] in [l] *)

  val count : ('a -> bool) -> 'a list -> int
  (** Count the number of elements satisfying a predicate *)

  (** {6 Finding position} *)

  val index : 'a eq -> 'a -> 'a list -> int
  (** [index] returns the 1st index of an element in a list (counting from 1). *)

  val safe_index : 'a eq -> 'a -> 'a list -> int option
  (** [safe_index] returns the 1st index of an element in a list (counting from 1)
      and None otherwise. *)

  val index0 : 'a eq -> 'a -> 'a list -> int
  (** [index0] behaves as [index] except that it starts counting at 0. *)

  (** {6 Folding} *)

  val fold_left_until : ('c -> 'a -> 'c CSig.until) -> 'c -> 'a list -> 'c
  (** acts like [fold_left f acc s] while [f] returns
      [Cont acc']; it stops returning [c] as soon as [f] returns [Stop c]. *)

  val fold_right_i :  (int -> 'a -> 'b -> 'b) -> int -> 'a list -> 'b -> 'b
  (** Like [List.fold_right] but with an index *)

  val fold_left_i :  (int -> 'a -> 'b -> 'a) -> int -> 'a -> 'b list -> 'a
  (** Like [List.fold_left] but with an index *)

  val fold_right_and_left : ('b -> 'a -> 'a list -> 'b) -> 'a list -> 'b -> 'b
  (** [fold_right_and_left f [a1;...;an] hd] is
      [f (f (... (f (f hd an [an-1;...;a1]) an-1 [an-2;...;a1]) ...) a2 [a1]) a1 []] *)

  val fold_left3 : ('a -> 'b -> 'c -> 'd -> 'a) -> 'a -> 'b list -> 'c list -> 'd list -> 'a
  (** Like [List.fold_left] but for 3 lists; raise [Invalid_argument _] if
      not all lists of the same size *)

  val fold_left2_set : exn -> ('a -> 'b -> 'c -> 'b list -> 'c list -> 'a) -> 'a -> 'b list -> 'c list -> 'a
  (** Fold sets, i.e. lists up to order; the folding function tells
      when elements match by returning a value and raising the given
      exception otherwise; sets should have the same size; raise the
      given exception if no pairing of the two sets is found;;
      complexity in O(n^2) *)

  val fold_left_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
  (** [fold_left_map f e_0 [a1;...;an]] is [e_n,[k_1...k_n]]
      where [(e_i,k_i)] is [f e_{i-1} ai] for each i<=n *)

  val fold_right_map : ('b -> 'a -> 'c * 'a) -> 'b list -> 'a -> 'c list * 'a
  (** Same, folding on the right *)

  val fold_left2_map : ('a -> 'b -> 'c -> 'a * 'd) -> 'a -> 'b list -> 'c list -> 'a * 'd list
  (** Same with two lists, folding on the left *)

  val fold_right2_map : ('b -> 'c -> 'a -> 'd * 'a) -> 'b list -> 'c list -> 'a -> 'd list * 'a
  (** Same with two lists, folding on the right *)

  val fold_left3_map : ('a -> 'b -> 'c -> 'd -> 'a * 'e) -> 'a -> 'b list -> 'c list -> 'd list -> 'a * 'e list
  (** Same with three lists, folding on the left *)

  val fold_left4_map : ('a -> 'b -> 'c -> 'd -> 'e -> 'a * 'r) -> 'a -> 'b list -> 'c list -> 'd list -> 'e list -> 'a * 'r list
  (** Same with four lists, folding on the left *)

  val fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
  [@@ocaml.deprecated "Same as [fold_left_map]"]

  val fold_map' : ('b -> 'a -> 'c * 'a) -> 'b list -> 'a -> 'c list * 'a
  [@@ocaml.deprecated "Same as [fold_right_map]"]

  (** {6 Splitting} *)

  val except : 'a eq -> 'a -> 'a list -> 'a list
  (** [except eq a l] Remove all occurrences of [a] in [l] *)

  val remove : 'a eq -> 'a -> 'a list -> 'a list
  (** Alias of [except] *)

  val remove_first : ('a -> bool) -> 'a list -> 'a list
  (** Remove the first element satisfying a predicate, or raise [Not_found] *)

  val extract_first : ('a -> bool) -> 'a list -> 'a list * 'a
  (** Remove and return the first element satisfying a predicate,
      or raise [Not_found] *)

  val find_map : ('a -> 'b option) -> 'a list -> 'b
  (** Returns the first element that is mapped to [Some _]. Raise [Not_found] if
      there is none. *)

  exception IndexOutOfRange
  val goto: int -> 'a list -> 'a list * 'a list
  (** [goto i l] splits [l] into two lists [(l1,l2)] such that
      [(List.rev l1)++l2=l] and [l1] has length [i].  It raises
      [IndexOutOfRange] when [i] is negative or greater than the
      length of [l]. *)

  val split_when : ('a -> bool) -> 'a list -> 'a list * 'a list
  (** [split_when p l] splits [l] into two lists [(l1,a::l2)] such that
      [l1++(a::l2)=l], [p a=true] and [p b = false] for every element [b] of [l1].
      if there is no such [a], then it returns [(l,[])] instead. *)

  val sep_last : 'a list -> 'a * 'a list
  (** [sep_last l] returns [(a,l')] such that [l] is [l'@[a]].
      It raises [Failure _] if the list is empty. *)

  val drop_last : 'a list -> 'a list
  (** Remove the last element of the list. It raises [Failure _] if the
      list is empty. This is the second part of [sep_last]. *)

  val last : 'a list -> 'a
  (** Return the last element of the list. It raises [Failure _] if the
      list is empty. This is the first part of [sep_last]. *)

  val lastn : int -> 'a list -> 'a list
  (** [lastn n l] returns the [n] last elements of [l]. It raises
      [Failure _] if [n] is less than 0 or larger than the length of [l] *)

  val chop : int -> 'a list -> 'a list * 'a list
  (** [chop i l] splits [l] into two lists [(l1,l2)] such that
      [l1++l2=l] and [l1] has length [i]. It raises [Failure _] when
      [i] is negative or greater than the length of [l]. *)

  val firstn : int -> 'a list -> 'a list
  (** [firstn n l] Returns the [n] first elements of [l]. It raises
      [Failure _] if [n] negative or too large. This is the first part
      of [chop]. *)

  val skipn : int -> 'a list -> 'a list
  (** [skipn n l] drops the [n] first elements of [l]. It raises
      [Failure _] if [n] is less than 0 or larger than the length of [l].
      This is the second part of [chop]. *)

  val skipn_at_least : int -> 'a list -> 'a list
  (** Same as [skipn] but returns [] if [n] is larger than the list of
      the list. *)

  val drop_prefix : 'a eq -> 'a list -> 'a list -> 'a list
  (** [drop_prefix eq l1 l] returns [l2] if [l=l1++l2] else return [l]. *)

  val insert : 'a eq -> 'a -> 'a list -> 'a list
  (** Insert at the (first) position so that if the list is ordered wrt to the
      total order given as argument, the order is preserved *)

  val share_tails : 'a list -> 'a list -> 'a list * 'a list * 'a list
  (** [share_tails l1 l2] returns [(l1',l2',l)] such that [l1] is
      [l1'\@l] and [l2] is [l2'\@l] and [l] is maximal amongst all such
      decompositions *)

  (** {6 Association lists} *)

  val map_assoc : ('a -> 'b) -> ('c * 'a) list -> ('c * 'b) list
  (** Applies a function on the codomain of an association list *)

  val assoc_f : 'a eq -> 'a -> ('a * 'b) list -> 'b
  (** Like [List.assoc] but using the equality given as argument *)

  val remove_assoc_f : 'a eq -> 'a -> ('a * 'b) list -> ('a * 'b) list
  (** Remove first matching element; unchanged if no such element *)

  val mem_assoc_f : 'a eq -> 'a -> ('a * 'b) list -> bool
  (** Like [List.mem_assoc] but using the equality given as argument *)

  val factorize_left : 'a eq -> ('a * 'b) list -> ('a * 'b list) list
  (** Create a list of associations from a list of pairs *)

  (** {6 Operations on lists of tuples} *)

  val split : ('a * 'b) list -> 'a list * 'b list
  (** Like OCaml's [List.split] but tail-recursive. *)

  val combine : 'a list -> 'b list -> ('a * 'b) list
  (** Like OCaml's [List.combine] but tail-recursive. *)

  val split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
  (** Like [split] but for triples *)

  val combine3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list
  (** Like [combine] but for triples *)

  (** {6 Operations on lists seen as sets, preserving uniqueness of elements} *)

  val add_set : 'a eq -> 'a -> 'a list -> 'a list
  (** [add_set x l] adds [x] in [l] if it is not already there, or returns [l]
      otherwise. *)

  val eq_set : 'a eq -> 'a list eq
  (** Test equality up to permutation. It respects multiple occurrences
      and thus works also on multisets. *)

  val subset : 'a list eq
  (** Tell if a list is a subset of another up to permutation. It expects
      each element to occur only once. *)

  val merge_set : 'a cmp -> 'a list -> 'a list -> 'a list
  (** Merge two sorted lists and preserves the uniqueness property. *)

  val intersect : 'a eq -> 'a list -> 'a list -> 'a list
  (** Return the intersection of two lists, assuming and preserving
      uniqueness of elements *)

  val union : 'a eq -> 'a list -> 'a list -> 'a list
  (** Return the union of two lists, assuming and preserving
      uniqueness of elements *)

  val unionq : 'a list -> 'a list -> 'a list
  (** [union] specialized to physical equality *)

  val subtract : 'a eq -> 'a list -> 'a list -> 'a list
  (** Remove from the first list all elements from the second list. *)

  val subtractq : 'a list -> 'a list -> 'a list
  (** [subtract] specialized to physical equality *)

  val merge_uniq : 'a cmp -> 'a list -> 'a list -> 'a list
  [@@ocaml.deprecated "Same as [merge_set]"]

  (** {6 Uniqueness and duplication} *)

  val distinct : 'a list -> bool
  (** Return [true] if all elements of the list are distinct. *)

  val distinct_f : 'a cmp -> 'a list -> bool
  (** Like [distinct] but using the equality given as argument *)

  val duplicates : 'a eq -> 'a list -> 'a list
  (** Return the list of unique elements which appear at least twice. Elements
      are kept in the order of their first appearance. *)

  val uniquize : 'a list -> 'a list
  (** Return the list of elements without duplicates.
      This is the list unchanged if there was none. *)

  val sort_uniquize : 'a cmp -> 'a list -> 'a list
  (** Return a sorted version of a list without duplicates
      according to some comparison function. *)

  val min : 'a cmp -> 'a list -> 'a
  (** Return minimum element according to some comparison function.

      @raise Not_found on an empty list. *)

  (** {6 Cartesian product} *)

  val cartesian : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  (** A generic binary cartesian product: for any operator (**),
    [cartesian (**) [x1;x2] [y1;y2] = [x1**y1; x1**y2; x2**y1; x2**y1]],
    and so on if there are more elements in the lists. *)

  val cartesians : ('a -> 'b -> 'b) -> 'b -> 'a list list -> 'b list
  (** [cartesians op init l] is an n-ary cartesian product: it builds
      the list of all [op a1 .. (op an init) ..] for [a1], ..., [an] in
      the product of the elements of the lists *)

  val combinations : 'a list list -> 'a list list
  (** [combinations l] returns the list of [n_1] * ... * [n_p] tuples
      [[a11;...;ap1];...;[a1n_1;...;apn_pd]] whenever [l] is a list
      [[a11;..;a1n_1];...;[ap1;apn_p]]; otherwise said, it is
      [cartesians (::) [] l] *)

  val cartesians_filter :
    ('a -> 'b -> 'b option) -> 'b -> 'a list list -> 'b list
  (** Like [cartesians op init l] but keep only the tuples for which
      [op] returns [Some _] on all the elements of the tuple. *)

  module Smart :
  sig
    val map : ('a -> 'a) -> 'a list -> 'a list
    (** [Smart.map f [a1...an] = List.map f [a1...an]] but if for all i
        [f ai == ai], then [Smart.map f l == l] *)
  end

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
