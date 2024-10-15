(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Primitive [string] type. *)

type t = private string

type char63 = Uint63.t

val max_length_int : int
val max_length : Uint63.t

(** [to_string s] converts the primitive string [s] into a standard string. *)
val to_string : t -> string

(** [of_string s] converts string [s] into a primitive string if its size does
    not exceed [max_length_int], and returns [None] otherwise. *)
val of_string : string -> t option

(** [make i c] returns a string of size [min i max_length] containing only the
    character with code [c l_and 255]. *)
val make : Uint63.t -> char63 -> t

(** [length s] gives the length of string [s]. *)
val length : t -> Uint63.t

(** [get s i] gives the code of the character stored at index [i] in [s]. When
    index [i] is invalid, the function returns zero. *)
val get : t -> Uint63.t -> char63

(** [sub s off len] returns the substring of [s] starting at offset [off], and
    of length [len], when possible. If [off] is not a valid offset in [s], the
    empty string is returned. If [off] is a valid offset, the function returns
    the longest possible suffix of [s] that: (1) starts at [off], and (2) does
    not have more than [len] characters. *)
val sub : t -> Uint63.t -> Uint63.t -> t

(** [cat s1 s2] returns the concatenation of [s1] and of the longest prefix of
    [s2] such that the sum of their lengths does not exceed [max_length]. *)
val cat : t -> t -> t

(** [compare s1 s2] returns [0] if [s1] and [s2] are equal, a number less than
    [0] if [s1] is smaller than [s2], and a number greater than [0] if [s1] is
    greater than [s2]. *)
val compare : t -> t -> int

(** [equal s1 s2] indicates whether [s1] and [s2] are equal. *)
val equal : t -> t -> bool

(** [hash s] gives a hash of [s], with the same value as [Hashtbl.hash s]. *)
val hash : t -> int

(** [unsafe_of_string s] converts [s] into a primitive string without checking
    whether its size satisfies the length constraint. Callers of this function
    must ensure that [length s <= max_length_int], which is always the case if
    [s] was obtained via [to_string]. NOTE: this function is used in generated
    code, via [compile]. *)
val unsafe_of_string : string -> t

(** [compile s] outputs an OCaml expression producing primitive string [s]. *)
val compile : t -> string
