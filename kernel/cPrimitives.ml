(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
  | Float64compare
  | Float64add
  | Float64sub
  | Float64mul
  | Float64div
  | Float64sqrt
  | Float64ofInt63
  | Float64normfr_mantissa
  | Float64frshiftexp
  | Float64ldshiftexp

let equal (p1 : t) (p2 : t) =
  p1 == p2

let hash = function
  | Int63head0 -> 1
  | Int63tail0 -> 2
  | Int63add -> 3
  | Int63sub -> 4
  | Int63mul -> 5
  | Int63div -> 6
  | Int63mod -> 7
  | Int63lsr -> 8
  | Int63lsl -> 9
  | Int63land -> 10
  | Int63lor -> 11
  | Int63lxor -> 12
  | Int63addc -> 13
  | Int63subc -> 14
  | Int63addCarryC -> 15
  | Int63subCarryC -> 16
  | Int63mulc -> 17
  | Int63diveucl -> 18
  | Int63div21 -> 19
  | Int63addMulDiv -> 20
  | Int63eq -> 21
  | Int63lt -> 22
  | Int63le -> 23
  | Int63compare -> 24
  | Float64opp -> 25
  | Float64abs -> 26
  | Float64compare -> 27
  | Float64add -> 28
  | Float64sub -> 29
  | Float64mul -> 30
  | Float64div -> 31
  | Float64sqrt -> 32
  | Float64ofInt63 -> 33
  | Float64normfr_mantissa -> 34
  | Float64frshiftexp -> 35
  | Float64ldshiftexp -> 36

(* Should match names in nativevalues.ml *)
let to_string = function
  | Int63head0 -> "head0"
  | Int63tail0 -> "tail0"
  | Int63add -> "add"
  | Int63sub -> "sub"
  | Int63mul -> "mul"
  | Int63div -> "div"
  | Int63mod -> "rem"
  | Int63lsr -> "l_sr"
  | Int63lsl -> "l_sl"
  | Int63land -> "l_and"
  | Int63lor -> "l_or"
  | Int63lxor -> "l_xor"
  | Int63addc -> "addc"
  | Int63subc -> "subc"
  | Int63addCarryC -> "addCarryC"
  | Int63subCarryC -> "subCarryC"
  | Int63mulc -> "mulc"
  | Int63diveucl -> "diveucl"
  | Int63div21 -> "div21"
  | Int63addMulDiv -> "addMulDiv"
  | Int63eq -> "eq"
  | Int63lt -> "lt"
  | Int63le -> "le"
  | Int63compare -> "compare"
  | Float64opp -> "fopp"
  | Float64abs -> "fabs"
  | Float64compare -> "fcompare"
  | Float64add -> "fadd"
  | Float64sub -> "fsub"
  | Float64mul -> "fmul"
  | Float64div -> "fdiv"
  | Float64sqrt -> "fsqrt"
  | Float64ofInt63 -> "float_of_int"
  | Float64normfr_mantissa -> "normfr_mantissa"
  | Float64frshiftexp -> "frshiftexp"
  | Float64ldshiftexp -> "ldshiftexp"

type prim_type =
  | PT_int63
  | PT_float64

type 'a prim_ind =
  | PIT_bool : unit prim_ind
  | PIT_carry : prim_type prim_ind
  | PIT_pair : (prim_type * prim_type) prim_ind
  | PIT_cmp : unit prim_ind
  | PIT_option : unit prim_ind

type prim_ind_ex = PIE : 'a prim_ind -> prim_ind_ex

type ind_or_type =
  | PITT_ind : 'a prim_ind * 'a -> ind_or_type
  | PITT_type : prim_type -> ind_or_type

let types =
  let int_ty = PITT_type PT_int63 in
  let float_ty = PITT_type PT_float64 in
  function
  | Int63head0 | Int63tail0 -> [int_ty; int_ty]
  | Int63add | Int63sub | Int63mul
  | Int63div | Int63mod
  | Int63lsr | Int63lsl
  | Int63land | Int63lor | Int63lxor -> [int_ty; int_ty; int_ty]
  | Int63addc | Int63subc | Int63addCarryC | Int63subCarryC ->
     [int_ty; int_ty; PITT_ind (PIT_carry, PT_int63)]
  | Int63mulc | Int63diveucl ->
     [int_ty; int_ty; PITT_ind (PIT_pair, (PT_int63, PT_int63))]
  | Int63eq | Int63lt | Int63le -> [int_ty; int_ty; PITT_ind (PIT_bool, ())]
  | Int63compare -> [int_ty; int_ty; PITT_ind (PIT_cmp, ())]
  | Int63div21 ->
     [int_ty; int_ty; int_ty; PITT_ind (PIT_pair, (PT_int63, PT_int63))]
  | Int63addMulDiv -> [int_ty; int_ty; int_ty; int_ty]
  | Float64opp | Float64abs | Float64sqrt -> [float_ty; float_ty]
  | Float64ofInt63 -> [int_ty; float_ty]
  | Float64normfr_mantissa -> [float_ty; int_ty]
  | Float64frshiftexp -> [float_ty; PITT_ind (PIT_pair, (PT_float64, PT_int63))]
  | Float64compare -> [float_ty; float_ty; PITT_ind (PIT_option, ())]
  | Float64add | Float64sub | Float64mul
  | Float64div -> [float_ty; float_ty; float_ty]
  | Float64ldshiftexp -> [float_ty; int_ty; float_ty]

type arg_kind =
  | Kparam (* not needed for the evaluation of the primitive when it reduces *)
  | Kwhnf  (* need to be reduced in whnf before reducing the primitive *)
  | Karg   (* no need to be reduced in whnf. example: [v] in [Array.set t i v] *)

type args_red = arg_kind list

(* Invariant only argument of type int63, float or an inductive can
   have kind Kwhnf *)

let arity t = List.length (types t) - 1

let kind t =
  let rec aux n = if n <= 0 then [] else Kwhnf :: aux (n - 1) in
  aux (arity t)

(** Special Entries for Register **)

type op_or_type =
  | OT_op of t
  | OT_type of prim_type

let prim_ind_to_string (type a) (p : a prim_ind) = match p with
  | PIT_bool -> "bool"
  | PIT_carry -> "carry"
  | PIT_pair -> "pair"
  | PIT_cmp -> "cmp"
  | PIT_option -> "option"

let prim_type_to_string = function
  | PT_int63 -> "int63_type"
  | PT_float64 -> "float64_type"

let op_or_type_to_string = function
  | OT_op op -> to_string op
  | OT_type t -> prim_type_to_string t
