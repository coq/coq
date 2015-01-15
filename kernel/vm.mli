open Names
open Term
open Cbytecodes

(** Efficient Virtual Machine *)

val set_drawinstr : unit -> unit

val transp_values : unit -> bool
val set_transp_values : bool -> unit

(** Machine code *)

type tcode

(** Values *)

type vprod
type vfun
type vfix
type vcofix
type vblock
type vswitch
type arguments

type atom =
  | Aid of Vars.id_key
  | Aiddef of Vars.id_key * values
  | Aind of pinductive

(** Zippers *)

type zipper =
  | Zapp of arguments
  | Zfix of vfix * arguments  (** might be empty *)
  | Zswitch of vswitch

type stack = zipper list

type to_up

type whd =
  | Vsort of sorts
  | Vprod of vprod
  | Vfun of vfun
  | Vfix of vfix * arguments option
  | Vcofix of vcofix * to_up * arguments option
  | Vconstr_const of int
  | Vconstr_block of vblock
  | Vatom_stk of atom * stack

(** Constructors *)

val val_of_str_const : structured_constant -> values
val val_of_rel : int -> values
val val_of_named : Id.t -> values
val val_of_constant : pconstant -> values

external val_of_annot_switch : annot_switch -> values = "%identity"

(** Destructors *)

val whd_val : values -> whd

(** Arguments *)

val nargs : arguments -> int
val arg : arguments -> int -> values

(** Product *)

val dom : vprod -> values
val codom : vprod -> vfun

(** Function *)

val body_of_vfun : int -> vfun -> values
val decompose_vfun2  : int -> vfun -> vfun -> int * values * values

(** Fix *)

val current_fix : vfix -> int
val check_fix : vfix -> vfix -> bool
val rec_args : vfix -> int array
val reduce_fix : int -> vfix -> vfun array * values array
                              (** bodies ,  types *)

(** CoFix *)

val current_cofix : vcofix -> int
val check_cofix : vcofix -> vcofix -> bool
val reduce_cofix : int -> vcofix -> values array * values array
                                      (** bodies , types *)

(** Block *)

val btag : vblock -> int
val bsize : vblock -> int
val bfield : vblock -> int -> values

(** Switch *)

val check_switch : vswitch -> vswitch -> bool
val case_info : vswitch -> case_info
val type_of_switch : vswitch -> values
val branch_of_switch : int -> vswitch -> (int * values) array

(** Evaluation *)

val whd_stack : values -> stack -> whd
val force_whd : values -> stack -> whd

val eta_whd : int -> whd -> values

