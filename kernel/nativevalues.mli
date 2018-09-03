(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Constr
open Names

(** This modules defines the representation of values internally used by
the native compiler. Be careful when removing apparently dead code from this
interface, as it may be used by programs generated at runtime. *)

type t = t -> t

type accumulator

type tag = int
type arity = int

type reloc_table = (tag * arity) array

type annot_sw = {
    asw_ind : inductive;
    asw_ci : case_info;
    asw_reloc : reloc_table;
    asw_finite : bool;
    asw_prefix : string
  }

val eq_annot_sw : annot_sw -> annot_sw -> bool

val hash_annot_sw : annot_sw -> int

type sort_annot = string * int
      
type rec_pos = int array

val eq_rec_pos : rec_pos -> rec_pos -> bool

type atom =
  | Arel of int
  | Aconstant of pconstant
  | Aind of pinductive
  | Asort of Sorts.t
  | Avar of Id.t
  | Acase of annot_sw * accumulator * t * (t -> t) 
  | Afix of t array * t array * rec_pos * int 
  | Acofix of t array * t array * int * t
  | Acofixe of t array * t array * int * t
  | Aprod of Name.t * t * (t -> t)
  | Ameta of metavariable * t
  | Aevar of Evar.t * t array (* arguments *)
  | Aproj of (inductive * int) * accumulator

(* Constructors *)

val mk_accu : atom -> t
val mk_rel_accu : int -> t
val mk_rels_accu : int -> int -> t array
val mk_constant_accu : Constant.t -> Univ.Level.t array -> t
val mk_ind_accu : inductive -> Univ.Level.t array -> t
val mk_sort_accu : Sorts.t -> Univ.Level.t array -> t
val mk_var_accu : Id.t -> t
val mk_sw_accu : annot_sw -> accumulator -> t -> (t -> t)
val mk_prod_accu : Name.t -> t -> t -> t
val mk_fix_accu : rec_pos  -> int -> t array -> t array -> t
val mk_cofix_accu : int -> t array -> t array -> t
val mk_meta_accu : metavariable -> t
val mk_evar_accu : Evar.t -> t array -> t
val mk_proj_accu : (inductive * int) -> accumulator -> t
val upd_cofix : t -> t -> unit
val force_cofix : t -> t 
val mk_const : tag -> t
val mk_block : tag -> t array -> t

val mk_bool : bool -> t
val mk_int : int -> t
val mk_uint : Uint31.t -> t

val napply : t -> t array -> t
(* Functions over accumulators *)

val dummy_value : unit -> t
val atom_of_accu : accumulator -> atom
val args_of_accu : accumulator -> t array
val accu_nargs : accumulator -> int

val cast_accu : t -> accumulator
(* Functions over block: i.e constructors *)
    
type block
      
val block_size : block -> int
val block_field : block -> int -> t
val block_tag : block -> int



(* kind_of_value *)

type kind_of_value =
  | Vaccu of accumulator
  | Vfun of (t -> t)
  | Vconst of int
  | Vblock of block

val kind_of_value : t -> kind_of_value

val str_encode : 'a -> string
val str_decode : string -> 'a

(** Support for machine integers *)

val val_to_int : t -> int
val is_int : t -> bool

(* function with check *)
val head0 : t -> t -> t
val tail0 : t -> t -> t

val add : t -> t -> t -> t
val sub : t -> t -> t -> t
val mul : t -> t -> t -> t
val div : t -> t -> t -> t
val rem : t -> t -> t -> t

val l_sr  : t -> t -> t -> t
val l_sl  : t -> t -> t -> t
val l_and : t -> t -> t -> t
val l_xor : t -> t -> t -> t
val l_or  : t -> t -> t -> t

val addc      : t -> t -> t -> t
val subc      : t -> t -> t -> t
val addcarryc : t -> t -> t -> t
val subcarryc : t -> t -> t -> t

val mulc    : t -> t -> t -> t
val diveucl : t -> t -> t -> t

val div21     : t -> t -> t -> t -> t
val addmuldiv : t -> t -> t -> t -> t

val eq      : t -> t -> t -> t
val lt      : t -> t -> t -> t
val le      : t -> t -> t -> t
val compare : t -> t -> t -> t 

(* Function without check *)
val no_check_head0 : t -> t
val no_check_tail0 : t -> t

val no_check_add : t -> t -> t
val no_check_sub : t -> t -> t
val no_check_mul : t -> t -> t
val no_check_div : t -> t -> t
val no_check_rem : t -> t -> t

val no_check_l_sr  : t -> t -> t
val no_check_l_sl  : t -> t -> t
val no_check_l_and : t -> t -> t
val no_check_l_xor : t -> t -> t
val no_check_l_or  : t -> t -> t

val no_check_addc      : t -> t -> t
val no_check_subc      : t -> t -> t
val no_check_addcarryc : t -> t -> t
val no_check_subcarryc : t -> t -> t

val no_check_mulc    : t -> t -> t
val no_check_diveucl : t -> t -> t

val no_check_div21     : t -> t -> t -> t
val no_check_addmuldiv : t -> t -> t -> t

val no_check_eq      : t -> t -> t
val no_check_lt      : t -> t -> t
val no_check_le      : t -> t -> t
val no_check_compare : t -> t -> t 

val mk_I31_accu : t
val decomp_uint : t -> t -> t
