open Names
open Term
open Cbytecodes
open Cemitcodes

(* option for virtual machine *)
val transp_values : unit -> bool
val set_transp_values : bool -> unit
val swap_global_transp : unit -> unit
(* le code machine *)
type tcode 

(* Les valeurs ***********)

type accumulator
type vprod 
type vfun
type vfix
type vfix_app
type vcofix
type vcofix_app 
type vblock
type vswitch
type arguments

type zipper =
  | Zapp of arguments
  | Zfix of vfix_app
  | Zswitch of vswitch

type stack = zipper list


type atom = 
  | Aid of id_key
  | Aiddef of id_key * values
  | Aind of inductive
  | Afix_app of accumulator * vfix_app
  | Aswitch of accumulator * vswitch

type whd =
  | Vsort of sorts
  | Vprod of vprod 
  | Vfun of vfun
  | Vfix of vfix
  | Vfix_app of vfix_app
  | Vcofix of vcofix
  | Vcofix_app of vcofix_app
  | Vconstr_const of int
  | Vconstr_block of vblock
  | Vatom_stk of atom * stack

(* Constructors *)
val val_of_str_const : structured_constant -> values

val val_of_rel : int -> values 
val val_of_rel_def : int -> values -> values 

val val_of_named : identifier -> values
val val_of_named_def : identifier -> values -> values

val val_of_constant : constant -> values 
val val_of_constant_def : constant -> values -> values

(* Destructors *)
val whd_val : values -> whd

(* Product *)
val dom : vprod -> values
val codom : vprod -> vfun
(* Function *)
val body_of_vfun : int -> vfun -> values 
val decompose_vfun2  : int -> vfun -> vfun -> int * values * values
(* Fix *)
val fix : vfix_app -> vfix
val args_of_fix : vfix_app -> arguments
val fix_init : vfix -> int
val fix_ndef : vfix -> int 
val rec_args : vfix -> int array 
val check_fix : vfix -> vfix -> bool
val bodies_of_fix : int -> vfix -> vfun array
val types_of_fix : vfix -> values array
(* CoFix *)
val cofix : vcofix_app -> vcofix
val args_of_cofix : vcofix_app -> arguments
val cofix_init : vcofix -> int 
val cofix_ndef : vcofix -> int
val check_cofix : vcofix -> vcofix -> bool
val bodies_of_cofix : int -> vcofix -> values array
val types_of_cofix : vcofix -> values array
(* Block *)
val btag : vblock -> int
val bsize : vblock -> int
val bfield : vblock -> int -> values
(* Switch *)
val eq_tbl : vswitch -> vswitch -> bool
val case_info : vswitch -> case_info
val type_of_switch : vswitch -> values
val branch_of_switch : int -> vswitch -> (int * values) array
(* Arguments *)  
val nargs : arguments -> int
val arg : arguments -> int -> values

(* Evaluation *)
val whd_stack : values -> stack -> whd



