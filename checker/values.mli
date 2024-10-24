(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type 'v kind = private
  | Any
  (** A value that we won't check, *)

  | Fail of string
  (** A value that shouldn't be there at all, *)

  | Tuple of string * 'v array
  (** A debug name and sub-values in this block *)

  | Sum of string * int * 'v array array
  (** A debug name, a number of constant constructors, and sub-values
     at each position of each possible constructed variant *)

  | Array of 'v
  | List of 'v
  | Opt of 'v
  | Int
  | String
  (** Builtin Ocaml types. *)

  | Annot of string * 'v
  (** Adds a debug note to the inner value *)

  | Int64
  | Float64

type value

val equal : value -> value -> bool

val kind : value -> value kind

val v_any : value
val v_fail : string -> value
val v_tuple : string -> value array -> value
val v_sum : string -> int -> value array array -> value
val v_array : value -> value
val v_list : value -> value
val v_opt : value -> value
val v_int : value
val v_string : value
val v_annot : string -> value -> value
val v_int64 : value
val v_float64 : value

(** Define a recursive value. [fix (fun v -> v)] is invalid. *)
val fix : (value -> value) -> value

val v_libsum : value
val v_lib : value
val v_opaquetable : value
val v_vmlib : value
