
(* $Id$ *)

(*i*)
open Pp
open Names
(* open Generic *)
open Term
open Evd
open Environ
(*i*)

(* Flags for profiling reductions. *)
val stats : bool ref
val share : bool ref


(*s The set of reduction kinds. *)
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


(*s Reduction function specification. *)

type red_mode = UNIFORM | SIMPL | WITHBACK

type flags = red_mode * reds

(* [(UNIFORM,r)]  == [r]-reduce in any context.
   [(SIMPL,r)]    == bdi-reduce under cases or fix, [r] otherwise 
   (like hnf does).
   [(WITHBACK,r)] == internal use: means we are under a case 
   or in rec. arg. of fix. *)

val flags_under : flags -> flags
val red_top : flags -> red_kind -> bool
val red_under : flags -> red_kind -> bool

val no_flag : flags
val beta : flags
val betaiota : flags
val betadeltaiota : flags

val hnf_flags : flags

(*s Explicit substitutions of type ['a]. [ESID] = identity. 
  [CONS(t,S)] = $S.t$ i.e. parallel substitution. [SHIFT(n,S)] = 
  $(\uparrow n~o~S)$ i.e. terms in S are relocated with n vars. 
  [LIFT(n,S)] = $(\%n~S)$ stands for $((\uparrow n~o~S).n...1)$. *)
type 'a subs =
  | ESID
  | CONS of 'a * 'a subs
  | SHIFT of int * 'a subs
  | LIFT of int * 'a subs

(*s Call by value functions *)
type cbv_value =
  | VAL of int * constr
  | LAM of name * constr * constr * cbv_value subs
  | FIXP of fixpoint * cbv_value subs * cbv_value list
  | COFIXP of cofixpoint * cbv_value subs * cbv_value list
  | CONSTR of int * (section_path * int) * cbv_value array * cbv_value list

val shift_value : int -> cbv_value -> cbv_value

(*i Private ??
val contract_fixp : cbv_value subs -> fixpoint -> cbv_value subs * constr
i*)

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
(*i Private ??
val fixp_reducible :
  (cbv_value -> cbv_value) -> flags -> fixpoint -> stack -> bool
i*)

(* normalization of a constr: the two functions to know... *)
type 'a cbv_infos
val create_cbv_infos : flags -> env -> 'a evar_map -> 'a cbv_infos
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


(*s Lazy reduction. *)

type freeze

type frterm =
  | FRel of int
  | FVAR of identifier
  | FOP0 of sorts oper
  | FOP1 of sorts oper * freeze
  | FOP2 of sorts oper * freeze * freeze
  | FOPN of sorts oper * freeze array
  | FLAM of name * freeze * constr * freeze subs
  | FLAMV of name * freeze array * constr array * freeze subs
  | FLam of name * type_freeze * freeze * constr * freeze subs
  | FPrd of name * type_freeze * freeze * constr * freeze subs
  | FLet of name * freeze * type_freeze * freeze * constr * freeze subs
  | FLIFT of int * freeze
  | FFROZEN of constr * freeze subs

and type_freeze = freeze

val frterm_of : freeze -> frterm
val is_val : freeze -> bool

val lift_frterm : int -> freeze -> freeze
val lift_freeze : int -> freeze -> freeze

val freeze : freeze subs -> constr -> freeze
val freeze_vect : freeze subs -> constr array -> freeze array
val freeze_list : freeze subs -> constr list -> freeze list

val traverse_term : freeze subs -> constr -> freeze
val lift_term_of_freeze : lift_spec -> freeze -> constr

(* Back to constr *)
val fstrong : (freeze -> freeze) -> lift_spec -> freeze -> constr
val term_of_freeze : freeze -> constr
val applist_of_freeze : freeze array -> constr list

(* contract a substitution *)
val contract_subst : int -> constr -> freeze subs -> freeze -> freeze


(* Calculus of Constructions *)
type fconstr = freeze
val inject : constr -> fconstr

val strip_frterm :
  int -> fconstr -> fconstr array list -> int * fconstr * fconstr array
val strip_freeze : fconstr -> int * fconstr * fconstr array


(* Auxiliary functions for (co)fixpoint reduction *)
val contract_fix_vect : (fconstr -> fconstr) -> frterm -> fconstr
val copy_case : case_info -> fconstr array -> fconstr -> fconstr


(* Iota analysis: reducible ? *)
type case_status =
  | CONSTRUCTOR of int * fconstr array
  | COFIX of int * int * fconstr array * fconstr array
  | IRREDUCTIBLE


(* Constant cache *)
type 'a clos_infos
val create_clos_infos : flags -> env -> 'a evar_map -> 'a clos_infos
val clos_infos_env : 'a clos_infos -> env

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
