(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open NumCompat

module Int : sig
  type t = int

  val compare : int -> int -> int
  val equal : int -> int -> bool
end

module ISet : sig
  include Set.S with type elt = int

  val pp : out_channel -> t -> unit
end

module IMap : sig
  include Map.S with type key = int

  (** [from k  m] returns the submap of [m] with keys greater or equal k *)
  val from : key -> 'elt t -> 'elt t
end

module Cmp : sig
  val compare_list : ('a -> 'b -> int) -> 'a list -> 'b list -> int
  val compare_lexical : (unit -> int) list -> int
end

module Tag : sig
  type t

  val pp : out_channel -> t -> unit
  val next : t -> t
  val max : t -> t -> t
  val from : int -> t
  val to_int : t -> int
  val compare : t -> t -> int
end

module TagSet : CSig.SetS with type elt = Tag.t

module McPrinter : sig
  module Mc = Micromega
  val pp_nat : out_channel -> Mc.nat -> unit
  val pp_positive : out_channel -> Mc.positive -> unit
  val pp_z : out_channel -> Mc.z -> unit
  val pp_pol : (out_channel -> 'a -> unit) -> out_channel -> 'a Mc.pol -> unit
  val pp_psatz : (out_channel -> 'a -> unit) -> out_channel -> 'a Mc.psatz -> unit
  val pp_proof_term : out_channel -> Mc.zArithProof -> unit
end
val pp_list :
  string -> (out_channel -> 'a -> unit) -> out_channel -> 'a list -> unit

module CamlToCoq : sig
  val positive : int -> Micromega.positive
  val bigint : Z.t -> Micromega.z
  val n : int -> Micromega.n
  val nat : int -> Micromega.nat
  val q : Q.t -> Micromega.q
  val index : int -> Micromega.positive
  val z : int -> Micromega.z
  val positive_big_int : Z.t -> Micromega.positive
end

module CoqToCaml : sig
  val z_big_int : Micromega.z -> Z.t
  val z : Micromega.z -> int
  val q_to_num : Micromega.q -> Q.t
  val positive : Micromega.positive -> int
  val n : Micromega.n -> int
  val nat : Micromega.nat -> int
  val index : Micromega.positive -> int
end

module Hash : sig
  val eq_op1 : Micromega.op1 -> Micromega.op1 -> bool
  val eq_op2 : Micromega.op2 -> Micromega.op2 -> bool
  val eq_positive : Micromega.positive -> Micromega.positive -> bool
  val eq_z : Micromega.z -> Micromega.z -> bool
  val eq_q : Micromega.q -> Micromega.q -> bool

  val eq_pol :
    ('a -> 'a -> bool) -> 'a Micromega.pol -> 'a Micromega.pol -> bool

  val eq_pair :
    ('a -> 'a -> bool) -> ('b -> 'b -> bool) -> 'a * 'b -> 'a * 'b -> bool

  val hash_op1 : int -> Micromega.op1 -> int
  val hash_pol : (int -> 'a -> int) -> int -> 'a Micromega.pol -> int

  val hash_pair :
    (int -> 'a -> int) -> (int -> 'b -> int) -> int -> 'a * 'b -> int

  val hash_z : int -> Micromega.z -> int
  val hash_q : int -> Micromega.q -> int
  val hash_string : int -> string -> int
  val hash_elt : ('a -> int) -> int -> 'a -> int
end

val all_pairs : ('a -> 'a -> 'b) -> 'a list -> 'b list
val try_any : (('a -> 'b option) * 'c) list -> 'a -> 'b option
val is_sublist : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
val extract : ('a -> 'b option) -> 'a list -> ('b * 'a) option * 'a list
val extract_all : ('a -> 'b option) -> 'a list -> 'b list * 'a list

val extract_best :
     ('a -> 'b option)
  -> ('b -> 'b -> bool)
  -> 'a list
  -> ('b * 'a) option * 'a list

val find_some : ('a -> 'b option) -> 'a list -> 'b option
val iterate_until_stable : ('a -> 'a option) -> 'a -> 'a
val simplify : ('a -> 'a option) -> 'a list -> 'a list option

val saturate :
  ('a -> 'b option) -> ('b * 'a -> 'a -> 'a option) -> 'a list -> 'a list

val saturate_bin :
     (module Set.S with type elt = 'a)
  -> ('a -> 'a -> 'a option)
  -> 'a list
  -> 'a list

val generate : ('a -> 'b option) -> 'a list -> 'b list
val app_funs : ('a -> 'b option) list -> 'a -> 'b option
val command : string -> string array -> 'a -> 'b
