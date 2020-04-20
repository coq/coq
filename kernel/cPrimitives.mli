(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t =
  | Int63head0
  | Int63tail0
  | Int63add
  | Int63sub
  | Int63mul
  | Int63div
  | Int63mod
  | Int63lsr
  | Int63lsl
  | Int63land
  | Int63lor
  | Int63lxor
  | Int63addc
  | Int63subc
  | Int63addCarryC
  | Int63subCarryC
  | Int63mulc
  | Int63diveucl
  | Int63div21
  | Int63addMulDiv
  | Int63eq
  | Int63lt
  | Int63le
  | Int63compare
  | Float64opp
  | Float64abs
  | Float64eq
  | Float64lt
  | Float64le
  | Float64compare
  | Float64classify
  | Float64add
  | Float64sub
  | Float64mul
  | Float64div
  | Float64sqrt
  | Float64ofInt63
  | Float64normfr_mantissa
  | Float64frshiftexp
  | Float64ldshiftexp
  | Float64next_up
  | Float64next_down

(** Can raise [Not_found].
    Beware that this is not exactly the reverse of [to_string] below. *)
val parse : string -> t

val equal : t -> t -> bool

type arg_kind =
  | Kparam (* not needed for the elavuation of the primitive*)
  | Kwhnf  (* need to be reduced in whnf before reducing the primitive *)
  | Karg   (* no need to be reduced in whnf *)

type args_red = arg_kind list

val hash : t -> int

val to_string : t -> string

val arity : t -> int

val kind : t -> args_red

(** Special Entries for Register **)

type prim_type =
  | PT_int63
  | PT_float64

(** Can raise [Not_found] *)
val prim_type_of_string : string -> prim_type
val prim_type_to_string : prim_type -> string

type 'a prim_ind =
  | PIT_bool : unit prim_ind
  | PIT_carry : prim_type prim_ind
  | PIT_pair : (prim_type * prim_type) prim_ind
  | PIT_cmp : unit prim_ind
  | PIT_f_cmp : unit prim_ind
  | PIT_f_class : unit prim_ind

type prim_ind_ex = PIE : 'a prim_ind -> prim_ind_ex

type op_or_type =
  | OT_op of t
  | OT_type of prim_type

val prim_ind_to_string : 'a prim_ind -> string

(** Can raise [Not_found] *)
val op_or_type_of_string : string -> op_or_type
val op_or_type_to_string : op_or_type -> string

val parse_op_or_type : ?loc:Loc.t -> string -> op_or_type

type ind_or_type =
  | PITT_ind : 'a prim_ind * 'a -> ind_or_type
  | PITT_type : prim_type -> ind_or_type

val types : t -> ind_or_type list
