
(*i $Id$ i*)

(*i*)
open Pp
open Names
open Term
open Evd
open Environ
(*i*)

(* Flags for profiling reductions. *)
val stats : bool ref
val share : bool ref

type evaluable_global_reference =
  | EvalVarRef of identifier
  | EvalConstRef of section_path

(*s Delta implies all consts (both global (= by
  [section_path]) and local (= by [Rel] or [Var])), all evars, and letin's.
  Rem: reduction of a Rel/Var bound to a term is Delta, but reduction of 
  a LetIn expression is Letin reduction *)

type red_kind =
  | BETA
  | DELTA
  | ZETA
  | EVAR
  | IOTA
  | CONST of section_path list
  | CONSTBUT of section_path list
  | VAR of identifier
  | VARBUT of identifier

(* Sets of reduction kinds. *)
type reds

val no_red : reds
val beta_red : reds
val betaiota_red : reds
val betadeltaiota_red : reds
val unfold_red : evaluable_global_reference -> reds

(* Tests if a reduction kind is set *)
val red_set : reds -> red_kind -> bool

(* Adds a reduction kind to a set *)
val red_add : reds -> red_kind -> reds

(* Gives the constant list *)
val red_get_const : reds -> bool * (evaluable_global_reference list)

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
val unfold_flags : evaluable_global_reference -> flags

(*s Explicit substitutions of type ['a]. [ESID n] = %n~END = bounded identity. 
  [CONS(t,S)] = $S.t$ i.e. parallel substitution. [SHIFT(n,S)] = 
  $(\uparrow n~o~S)$ i.e. terms in S are relocated with n vars. 
  [LIFT(n,S)] = $(\%n~S)$ stands for $((\uparrow n~o~S).n...1)$. *)
type 'a subs =
  | ESID of int
  | CONS of 'a * 'a subs
  | SHIFT of int * 'a subs
  | LIFT of int * 'a subs

(*s A [stack] is a context of arguments, arguments are pushed by
   [append_stack] one array at a time but popped with [decomp_stack]
   one by one *)

type 'a stack
val empty_stack : 'a stack
val append_stack : 'a array -> 'a stack -> 'a stack
val decomp_stack : 'a stack -> ('a * 'a stack) option
val list_of_stack : 'a stack -> 'a list
val array_of_stack : 'a stack -> 'a array
val stack_assign : 'a stack -> int -> 'a -> 'a stack
val stack_args_size : 'a stack -> int
val app_stack : constr * constr stack -> constr
val stack_tail : int -> 'a stack -> 'a stack
val stack_nth : 'a stack -> int -> 'a

(***********************************************************************)
(*s Call-by-value reduction *)

(* Entry point for cbv normalization of a constr *)
type 'a cbv_infos
val create_cbv_infos : flags -> env -> 'a evar_map -> 'a cbv_infos
val cbv_norm : 'a cbv_infos -> constr -> constr

(*s Lazy reduction. *)

(* [fconstr] is the type of frozen constr *)

type fconstr

(* [fconstr] can be accessed by using the function [frterm_of] and by
   matching on type [frterm] *)

type frterm =
  | FRel of int
  | FAtom of constr
  | FCast of fconstr * fconstr
  | FFlex of frreference
  | FInd of inductive_path * fconstr array
  | FConstruct of constructor_path * fconstr array
  | FApp of fconstr * fconstr array
  | FFix of (int array * int) * (fconstr array * name list * fconstr array)
      * constr array * fconstr subs
  | FCoFix of int * (fconstr array * name list * fconstr array)
      * constr array * fconstr subs
  | FCases of case_info * fconstr * fconstr * fconstr array
  | FLambda of name * fconstr * fconstr * constr * fconstr subs
  | FProd of name * fconstr * fconstr * constr * fconstr subs
  | FLetIn of name * fconstr * fconstr * fconstr * constr * fconstr subs
  | FLIFT of int * fconstr
  | FFROZEN of constr * fconstr subs

and frreference =
  | FConst of section_path * fconstr array
  | FEvar of (existential * fconstr subs)
  | FVar of identifier
  | FFarRel of int

val frterm_of : fconstr -> frterm

(* To lazy reduce a constr, create a ['a clos_infos] with
   [create_cbv_infos], inject the term to reduce with [inject]; then use
   a reduction function *)

(* Global and local constant cache *)
type 'a clos_infos
val create_clos_infos : flags -> env -> 'a evar_map -> 'a clos_infos
val clos_infos_env : 'a clos_infos -> env

val inject : constr -> fconstr

(* Reduction function *)

(* [norm_val] is for strong normalization *)
val norm_val : 'a clos_infos -> fconstr -> constr

(* [whd_val] is for weak head normalization *)
val whd_val : 'a clos_infos -> fconstr -> constr

(* [fhnf] and [fnf_apply] are for weak head normalization but staying
   in [fcontr] world to perform step by step weak head normalization *)

val fhnf: 'a clos_infos -> fconstr -> int * fconstr * fconstr stack
val fhnf_apply : 'a clos_infos ->
  int -> fconstr -> fconstr stack -> int * fconstr * fconstr stack

(* [search_frozen_value] unfolds references in a [fconstr] *)
val search_frozen_value : 'a clos_infos -> frreference -> fconstr option


(*i This is for cbv debug *)
type cbv_value =
  | VAL of int * constr
  | LAM of name * constr * constr * cbv_value subs
  | FIXP of fixpoint * cbv_value subs * cbv_value list
  | COFIXP of cofixpoint * cbv_value subs * cbv_value list
  | CONSTR of int * (section_path * int) * cbv_value array * cbv_value list

val shift_value : int -> cbv_value -> cbv_value

type cbv_stack =
  | TOP
  | APP of cbv_value list * cbv_stack
  | CASE of constr * constr array * case_info * cbv_value subs * cbv_stack

val stack_app : cbv_value list -> cbv_stack -> cbv_stack
val under_case_stack : cbv_stack -> bool
val strip_appl : cbv_value -> cbv_stack -> cbv_value * cbv_stack

val red_allowed : flags -> cbv_stack -> red_kind -> bool
val reduce_const_body :
  (cbv_value -> cbv_value) -> cbv_value -> cbv_stack -> cbv_value * cbv_stack

(* recursive functions... *)
val cbv_stack_term : 'a cbv_infos ->
  cbv_stack -> cbv_value subs -> constr -> cbv_value
val cbv_norm_term : 'a cbv_infos -> cbv_value subs -> constr -> constr
val cbv_norm_more : 'a cbv_infos -> cbv_value subs -> cbv_value -> cbv_value
val norm_head : 'a cbv_infos ->
  cbv_value subs -> constr -> cbv_stack -> cbv_value * cbv_stack
val apply_stack : 'a cbv_infos -> constr -> cbv_stack -> constr
val cbv_norm_value : 'a cbv_infos -> cbv_value -> constr
(* End of cbv debug section i*)

(*i This is for lazy debug *)
type freeze = fconstr
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

val strip_frterm :
  int -> fconstr -> fconstr stack -> int * fconstr * fconstr stack
val strip_freeze : fconstr -> int * fconstr * fconstr stack

(* Auxiliary functions for (co)fixpoint reduction *)
val contract_fix_vect : frterm -> fconstr
val copy_case : case_info -> fconstr -> fconstr -> fconstr array -> fconstr

(* Iota analysis: reducible ? *)
type case_status =
  | CONSTRUCTOR of int * fconstr stack
  | COFIX of int * int * (fconstr array * name list * fconstr array) *
      fconstr stack * constr array * freeze subs
  | IRREDUCTIBLE

(* recursive functions... *)
val unfreeze : 'a clos_infos -> fconstr -> fconstr
val whnf_frterm : 'a clos_infos -> fconstr -> fconstr
val whnf_term : 'a clos_infos -> fconstr subs -> constr -> fconstr
val whnf_apply : 'a clos_infos -> fconstr -> fconstr stack -> fconstr

(* End of cbn debug section i*)
