
(* $Id$ *)

open Pp
open Names
open Generic
open Term
open Evd
open Environ

(* flags for profiling... *)
val stats : bool ref
val share : bool ref


(* sets of reduction kinds *)
type red_kind = BETA | DELTA of sorts oper | IOTA

type reds = { 
  r_beta : bool;
  r_delta : sorts oper -> bool;
  r_iota : bool }

val no_red : reds
val beta_red : reds
val betaiota_red : reds
val betadeltaiota_red : reds

val red_set : reds -> red_kind -> bool


(* reduction function specification *)

type red_mode = UNIFORM | SIMPL | WITHBACK

type flags = red_mode * reds

(* (UNIFORM,r)  == r-reduce in any context
 * (SIMPL,r)    == bdi-reduce under cases or fix, r otherwise (like hnf does)
 * (WITHBACK,r) == internal use: means we are under a case 
 *                 or in rec. arg. of fix *)

val flags_under : flags -> flags
val red_top : flags -> red_kind -> bool
val red_under : flags -> red_kind -> bool

val no_flag : flags
val beta : flags
val betaiota : flags
val betadeltaiota : flags

val hnf_flags : flags


(* Call by value functions *)
type cbv_value =
  | VAL of int * constr
  | LAM of name * constr * constr * cbv_value subs
  | FIXP of sorts oper * constr array * cbv_value subs * cbv_value list
  | CONSTR of int * (section_path * int) * cbv_value array * cbv_value list

val shift_value : int -> cbv_value -> cbv_value
val contract_fixp : cbv_value subs -> constr -> cbv_value subs * constr


type stack =
  | TOP
  | APP of cbv_value list * stack
  | CASE of constr * constr array * case_info * cbv_value subs * stack

val stack_app : cbv_value list -> stack -> stack
val under_case_stack : stack -> bool
val strip_appl : cbv_value -> stack -> cbv_value * stack

val red_allowed : flags -> stack -> red_kind -> bool
val reduce_const_body :
  (cbv_value -> cbv_value) -> cbv_value -> stack -> cbv_value * stack
val fixp_reducible :
  (cbv_value -> cbv_value) -> flags -> sorts oper -> stack -> bool

(* normalization of a constr: the two functions to know... *)
type 'a cbv_infos
val create_cbv_infos : flags -> 'a unsafe_env -> 'a cbv_infos
val cbv_norm : 'a cbv_infos -> constr -> constr

(* recursive functions... *)
val cbv_stack_term : 'a cbv_infos ->
  stack -> cbv_value subs -> constr -> cbv_value
val cbv_norm_term : 'a cbv_infos -> cbv_value subs -> constr -> constr
val cbv_norm_more : 'a cbv_infos -> cbv_value -> cbv_value
val norm_head : 'a cbv_infos ->
  cbv_value subs -> constr -> stack -> cbv_value * stack
val apply_stack : 'a cbv_infos -> constr -> stack -> constr
val cbv_norm_value : 'a cbv_infos -> cbv_value -> constr





(* Lazy reduction
 *)
type 'a freeze
type 'a frterm =
  | FRel of int
  | FVAR of identifier
  | FOP0 of 'a
  | FOP1 of 'a * 'a freeze
  | FOP2 of 'a * 'a freeze * 'a freeze
  | FOPN of 'a * 'a freeze array
  | FOPL of 'a * 'a freeze list
  | FLAM of name * 'a freeze * 'a term * 'a freeze subs
  | FLAMV of name * 'a freeze array * 'a term array * 'a freeze subs
  | FLIFT of int * 'a freeze
  | FFROZEN of 'a term * 'a freeze subs

val frterm_of : 'a freeze -> 'a frterm
val is_val : 'a freeze -> bool

val lift_frterm : int -> 'a freeze -> 'a freeze
val lift_freeze : int -> 'a freeze -> 'a freeze

val freeze : 'a freeze subs -> 'a term -> 'a freeze
val freeze_vect : 'a freeze subs -> 'a term array -> 'a freeze array
val freeze_list : 'a freeze subs -> 'a term list -> 'a freeze list

val traverse_term : 'a freeze subs -> 'a term -> 'a freeze
val lift_term_of_freeze : lift_spec -> 'a freeze -> 'a term

(* Back to constr *)
val fstrong : ('a freeze -> 'a freeze) -> lift_spec -> 'a freeze -> 'a term
val term_of_freeze : 'a freeze -> 'a term
val applist_of_freeze : 'a freeze array -> 'a term list

(* contract a substitution *)
val contract_subst : int -> 'a freeze -> 'a freeze -> 'a freeze


(* Calculus of Constructions *)
type fconstr = sorts oper freeze
val inject : constr -> fconstr
(* A pseudo-printer for fconstr *)
val prfconstr : fconstr -> std_ppcmds

val strip_frterm :
  int -> fconstr -> fconstr array list -> int * fconstr * fconstr array
val strip_freeze : fconstr -> int * fconstr * fconstr array


(* Auxiliary functions for (co)fixpoint reduction *)
val contract_fix_vect : (fconstr -> fconstr) -> sorts oper frterm -> fconstr
val copy_case : case_info -> fconstr array -> fconstr -> fconstr


(* Iota analysis: reducible ? *)
type case_status =
  | CONSTRUCTOR of int * fconstr array
  | COFIX of int * int * fconstr array * fconstr array
  | IRREDUCTIBLE


(* Constant cache *)
type 'a clos_infos
val create_clos_infos : flags -> 'a unsafe_env -> 'a clos_infos

(* Reduction function *)
val norm_val : 'a clos_infos -> fconstr -> constr
val whd_val : 'a clos_infos -> fconstr -> constr
val fhnf: 'a clos_infos -> fconstr -> int * fconstr * fconstr array
val fhnf_apply : 'a clos_infos ->
  int -> fconstr -> fconstr array -> int * fconstr * fconstr array
val search_frozen_cst : 'a clos_infos ->
  sorts oper -> fconstr array -> fconstr option

(* recursive functions... *)
val unfreeze : 'a clos_infos -> fconstr -> fconstr
val whnf_frterm : 'a clos_infos -> fconstr -> fconstr
val whnf_term : 'a clos_infos -> fconstr subs -> constr -> fconstr
val whnf_apply : 'a clos_infos -> fconstr -> fconstr array -> fconstr
