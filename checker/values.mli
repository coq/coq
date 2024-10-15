(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type value =
  | Any
  (** A value that we won't check, *)

  | Fail of string
  (** A value that shouldn't be there at all, *)

  | Tuple of string * value array
  (** A debug name and sub-values in this block *)

  | Sum of string * int * value array array
  (** A debug name, a number of constant constructors, and sub-values
     at each position of each possible constructed variant *)

  | Array of value
  | List of value
  | Opt of value
  | Int
  | String
  (** Builtin Ocaml types. *)

  | Annot of string * value
  (** Adds a debug note to the inner value *)

  | Dyn
  (** Coq's Dyn.t *)

  | Proxy of value ref
  (** Same as the inner value, used to define recursive types *)

  | Int64
  | Float64

(** NB: List and Opt have their own constructors to make it easy to
   define eg [let rec foo = List foo]. *)

val v_libsum : value
val v_lib : value
val v_opaquetable : value
val v_vmlib : value
