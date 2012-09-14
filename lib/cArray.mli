(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** FIXME: From OCaml 3.12 onwards, that would only be a [module type of] *)

module type S =
sig
  external length : 'a array -> int = "%array_length"
  external get : 'a array -> int -> 'a = "%array_safe_get"
  external set : 'a array -> int -> 'a -> unit = "%array_safe_set"
  external make : int -> 'a -> 'a array = "caml_make_vect"
  external create : int -> 'a -> 'a array = "caml_make_vect"
  val init : int -> (int -> 'a) -> 'a array
  val make_matrix : int -> int -> 'a -> 'a array array
  val create_matrix : int -> int -> 'a -> 'a array array
  val append : 'a array -> 'a array -> 'a array
  val concat : 'a array list -> 'a array
  val sub : 'a array -> int -> int -> 'a array
  val copy : 'a array -> 'a array
  val fill : 'a array -> int -> int -> 'a -> unit
  val blit : 'a array -> int -> 'a array -> int -> int -> unit
  val to_list : 'a array -> 'a list
  val of_list : 'a list -> 'a array
  val iter : ('a -> unit) -> 'a array -> unit
  val map : ('a -> 'b) -> 'a array -> 'b array
  val iteri : (int -> 'a -> unit) -> 'a array -> unit
  val mapi : (int -> 'a -> 'b) -> 'a array -> 'b array
  val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b array -> 'a
  val fold_right : ('b -> 'a -> 'a) -> 'b array -> 'a -> 'a
  val sort : ('a -> 'a -> int) -> 'a array -> unit
  val stable_sort : ('a -> 'a -> int) -> 'a array -> unit
  val fast_sort : ('a -> 'a -> int) -> 'a array -> unit
  external unsafe_get : 'a array -> int -> 'a = "%array_unsafe_get"
  external unsafe_set : 'a array -> int -> 'a -> unit = "%array_unsafe_set"
end

module type ExtS =
sig
  include S
  val compare : ('a -> 'a -> int) -> 'a array -> 'a array -> int
  val equal : ('a -> 'a -> bool) -> 'a array -> 'a array -> bool
  val exists : ('a -> bool) -> 'a array -> bool
  val for_all : ('a -> bool) -> 'a array -> bool
  val for_all2 : ('a -> 'b -> bool) -> 'a array -> 'b array -> bool
  val for_all3 : ('a -> 'b -> 'c -> bool) ->
    'a array -> 'b array -> 'c array -> bool
  val for_all4 : ('a -> 'b -> 'c -> 'd -> bool) ->
    'a array -> 'b array -> 'c array -> 'd array -> bool
  val for_all_i : (int -> 'a -> bool) -> int -> 'a array -> bool
  val find_i : (int -> 'a -> bool) -> 'a array -> int option
  val hd : 'a array -> 'a
  val tl : 'a array -> 'a array
  val last : 'a array -> 'a
  val cons : 'a -> 'a array -> 'a array
  val rev : 'a array -> unit
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
  val fold_right_from : int -> ('a -> 'b -> 'b) -> 'a array -> 'b -> 'b
  val app_tl : 'a array -> 'a list -> 'a list
  val list_of_tl : 'a array -> 'a list
  val map_to_list : ('a -> 'b) -> 'a array -> 'b list
  val chop : int -> 'a array -> 'a array * 'a array
  val smartmap : ('a -> 'a) -> 'a array -> 'a array
  val map2 : ('a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
  val map2_i : (int -> 'a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
  val map3 :
    ('a -> 'b -> 'c -> 'd) -> 'a array -> 'b array -> 'c array -> 'd array
  val map_left : ('a -> 'b) -> 'a array -> 'b array
  val map_left_pair : ('a -> 'b) -> 'a array -> ('c -> 'd) -> 'c array ->
    'b array * 'd array
  val iter2 : ('a -> 'b -> unit) -> 'a array -> 'b array -> unit
  val fold_map' : ('a -> 'c -> 'b * 'c) -> 'a array -> 'c -> 'b array * 'c
  val fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b array -> 'a * 'c array
  val fold_map2' :
    ('a -> 'b -> 'c -> 'd * 'c) -> 'a array -> 'b array -> 'c -> 'd array * 'c
  val distinct : 'a array -> bool
  val union_map : ('a -> 'b -> 'b) -> 'a array -> 'b -> 'b
  val rev_to_list : 'a array -> 'a list
  val filter_along : ('a -> bool) -> 'a list -> 'b array -> 'b array
  val filter_with : bool list -> 'a array -> 'a array
end

include ExtS
