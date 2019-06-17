(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Int : sig type t = int val compare : int -> int -> int val equal : int -> int -> bool end


module ISet : sig
  include Set.S with type elt = int
  val pp : out_channel -> t -> unit
end

module IMap :
sig
  include Map.S with type key = int

  (** [from k  m] returns the submap of [m] with keys greater or equal k *)
  val from : key -> 'elt t -> 'elt t

end

val numerator : Num.num -> Big_int.big_int
val denominator : Num.num -> Big_int.big_int

module Cmp : sig

  val compare_list : ('a -> 'b -> int) -> 'a list -> 'b list -> int
  val compare_lexical : (unit -> int) list -> int

end

module Tag : sig

  type t

  val pp : out_channel -> t -> unit
  val next : t -> t
  val max  :  t -> t -> t
  val from : int -> t
  val to_int : t -> int

end

module TagSet : CSig.SetS with type elt = Tag.t

val pp_list : string -> (out_channel -> 'a -> unit) -> out_channel -> 'a list -> unit

module CamlToCoq : sig

  val positive : int -> Micromega.positive
  val bigint : Big_int.big_int -> Micromega.z
  val n : int -> Micromega.n
  val nat : int -> Micromega.nat
  val q : Num.num -> Micromega.q
  val index : int -> Micromega.positive
  val z : int -> Micromega.z
  val positive_big_int : Big_int.big_int -> Micromega.positive

end

module CoqToCaml : sig

  val z_big_int : Micromega.z -> Big_int.big_int
  val q_to_num : Micromega.q -> Num.num
  val positive : Micromega.positive -> int
  val n : Micromega.n -> int
  val nat : Micromega.nat -> int
  val index : Micromega.positive -> int

end

val ppcm : Big_int.big_int -> Big_int.big_int -> Big_int.big_int

val all_pairs : ('a -> 'a -> 'b) -> 'a list -> 'b list
val try_any : (('a -> 'b option) * 'c) list -> 'a -> 'b option
val is_sublist : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool

val extract : ('a -> 'b option) -> 'a list -> ('b * 'a) option * 'a list

val extract_all : ('a -> 'b option) -> 'a list -> ('b * 'a) list * 'a list

val extract_best : ('a -> 'b option) -> ('b -> 'b -> bool) -> 'a list -> ('b *'a) option * 'a list

val find_some : ('a -> 'b option) -> 'a list  -> 'b option

val iterate_until_stable : ('a -> 'a option) -> 'a -> 'a

val simplify : ('a -> 'a option) -> 'a list -> 'a list option

val saturate : ('a -> 'b option) -> ('b * 'a -> 'a -> 'a option) -> 'a list -> 'a list

val generate : ('a -> 'b option) -> 'a list -> 'b list

val app_funs : ('a -> 'b option) list -> 'a -> 'b option

val command : string -> string array -> 'a -> 'b
