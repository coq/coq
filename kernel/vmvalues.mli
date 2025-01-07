(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** Values *)

type values
type structured_values
type vm_env
type vprod
type vfun
type vfix
type vcofix
type vblock
type arguments
type vstack = values array
type to_update

type tag = int

val type_atom_tag : tag
val max_atom_tag : tag
val proj_tag : tag
val fix_app_tag : tag
val switch_tag : tag
val cofix_tag : tag
val cofix_evaluated_tag : tag

type structured_constant =
  | Const_sort of Sorts.t
  | Const_ind of inductive
  | Const_evar of Evar.t
  | Const_b0 of tag
  | Const_univ_instance of UVars.Instance.t
  | Const_val of structured_values
  | Const_uint of Uint63.t
  | Const_float of Float64.t
  | Const_string of Pstring.t

val pp_struct_const : structured_constant -> Pp.t

type reloc_table = (tag * int) array

type annot_switch =
   { rtbl : reloc_table; tailcall : bool; max_stack_size : int }

val eq_structured_constant : structured_constant -> structured_constant -> bool
val hash_structured_constant : structured_constant -> int

val eq_annot_switch : annot_switch -> annot_switch -> bool
val hash_annot_switch : annot_switch -> int

val fun_val : vfun -> values
val fix_val : vfix -> values
val cofix_upd_val : to_update -> values

val inj_env : values array -> vm_env
val fun_env : vfun -> vm_env
val fix_env : vfix -> vm_env
val cofix_env : vcofix -> vm_env
val cofix_upd_env : to_update -> vm_env

(** Cast a value known to be a function, unsafe in general *)
val fun_of_val : values -> vfun

val crazy_val : values

(** Machine code *)

type tcode

type vswitch = {
    sw_type_code : tcode;
    sw_code : tcode;
    sw_annot : annot_switch;
    sw_stk : vstack;
    sw_env : vm_env
  }

external mkAccuCode : int -> tcode = "rocq_makeaccu"

val fun_code : vfun -> tcode
val fix_code : vfix -> tcode
val cofix_upd_code : to_update -> tcode

type id_key =
| ConstKey of Constant.t
| VarKey of Id.t
| RelKey of Int.t
| EvarKey of Evar.t

val eq_id_key : id_key -> id_key -> bool

type atom =
  | Aid of id_key
  | Aind of inductive
  | Asort of Sorts.t

val get_atom_rel : unit -> atom array
(** Global table of rels *)

(** Zippers *)

type zipper =
  | Zapp of arguments
  | Zfix of vfix * arguments  (** might be empty *)
  | Zswitch of vswitch
  | Zproj of int (* index of the projection as in Projection.Repr *)

type stack = zipper list

type accumulator = atom * stack

type kind = (values, accumulator, vfun, vprod, vfix * arguments option, vcofix * to_update * arguments option, vblock) Values.kind

(** For debugging purposes only *)

val pr_atom : atom -> Pp.t
val pr_kind : kind -> Pp.t
val pr_stack : stack -> Pp.t

(** Constructors *)

val val_of_str_const : structured_constant -> values
val val_of_rel : int -> values
val val_of_named : Id.t -> values
val val_of_constant : Constant.t -> values
val val_of_evar : Evar.t -> values
val val_of_proj : int -> values -> values
val val_of_atom : atom -> values
val val_of_int : int -> structured_values
val val_of_block : tag -> structured_values array -> structured_values
val val_of_uint : Uint63.t -> structured_values
val val_of_float : Float64.t -> structured_values
val val_of_string : Pstring.t -> structured_values

external val_of_annot_switch : annot_switch -> values = "%identity"

(** Destructors *)

val whd_val : values -> kind
val uni_instance : values -> UVars.Instance.t

(** Arguments *)

val nargs : arguments -> int
val arg : arguments -> int -> values

(** Product *)

val dom : vprod -> values
val codom : vprod -> vfun

(** Fun *)
external closure_arity : vfun -> int = "rocq_closure_arity"

(** Fix *)

val current_fix : vfix -> int
val check_fix : vfix -> vfix -> bool
val rec_args : vfix -> int array
val first_fix : vfix -> vfix
val fix_types : vfix -> tcode array
val cofix_types : vcofix -> tcode array
val mk_fix_body : int -> int -> vfix -> vfun array

(** CoFix *)

val current_cofix : vcofix -> int
val check_cofix : vcofix -> vcofix -> bool
val mk_cofix_body : (vfun -> vstack -> values) -> int -> int -> vcofix -> values array

(** Block *)

val btag  : vblock -> int
val bsize : vblock -> int
val bfield : vblock -> int -> values

(** Switch *)

val check_switch : vswitch -> vswitch -> bool
val branch_arg : int -> tag * int -> values

(** Primitives implemented in OCaml, seen as values (to be used as globals) *)
val parray_make : values
val parray_get : values
val parray_get_default : values
val parray_set : values
val parray_copy : values
val parray_length : values

val pstring_make : values
val pstring_length : values
val pstring_get : values
val pstring_sub : values
val pstring_cat : values
val pstring_compare : values
