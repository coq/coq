(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Names
open Term
open Environ
open Esubst
(*i*)

(* Flags for profiling reductions. *)
val stats : bool ref
val share : bool ref

val with_stats: 'a Lazy.t -> 'a

type evaluable_global_reference =
  | EvalVarRef of identifier
  | EvalConstRef of section_path

(*s Delta implies all consts (both global (= by
  [section_path]) and local (= by [Rel] or [Var])), all evars, and letin's.
  Rem: reduction of a Rel/Var bound to a term is Delta, but reduction of 
  a LetIn expression is Letin reduction *)

type transparent_state = Idpred.t * Sppred.t

val all_opaque      : transparent_state
val all_transparent : transparent_state

(* Sets of reduction kinds. *)
module type RedFlagsSig = sig
  type reds
  type red_kind

  (* The different kind of reduction *)
  (* Const/Var means the reference as argument should be unfolded *)
  (* Constbut/Varbut means all references except the ones as argument
     of Constbut/Varbut should be unfolded (there may be several such
     Constbut/Varbut *)
  val fBETA : red_kind
  val fDELTA : red_kind
  val fIOTA : red_kind
  val fZETA : red_kind
  val fCONST : section_path -> red_kind
  val fVAR : identifier -> red_kind

  (* No reduction at all *)
  val no_red : reds

  (* Adds a reduction kind to a set *)
  val red_add : reds -> red_kind -> reds

  (* Removes a reduction kind to a set *)
  val red_sub : reds -> red_kind -> reds

  (* Adds a reduction kind to a set *)
  val red_add_transparent : reds -> transparent_state -> reds

  (* Build a reduction set from scratch = iter [red_add] on [no_red] *)
  val mkflags : red_kind list -> reds

  (* Tests if a reduction kind is set *)
  val red_set : reds -> red_kind -> bool

  (* Gives the constant list *)
  val red_get_const : reds -> bool * evaluable_global_reference list
end

module RedFlags : RedFlagsSig
open RedFlags

val beta_red : reds
val betaiota_red : reds
val betadeltaiota_red : reds
val betaiotazeta_red : reds
val betadeltaiotanolet_red : reds

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
val betadeltaiotanolet : flags

val hnf_flags : flags
val unfold_flags : evaluable_global_reference -> flags

(***********************************************************************)

type table_key =
  | ConstKey of constant
  | VarKey of identifier
  | FarRelKey of int
   (* FarRel: index in the rel_context part of _initial_ environment *)

type 'a infos
val ref_value_cache: 'a infos -> table_key -> 'a option
val info_flags: 'a infos -> flags
val infos_under: 'a infos -> 'a infos
val create: ('a infos -> constr -> 'a) -> flags -> env -> 'a infos

(***********************************************************************)
(*s A [stack] is a context of arguments, arguments are pushed by
   [append_stack] one array at a time but popped with [decomp_stack]
   one by one *)

type 'a stack_member =
  | Zapp of 'a list
  | Zcase of case_info * 'a * 'a array
  | Zfix of 'a * 'a stack
  | Zshift of int
  | Zupdate of 'a

and 'a stack = 'a stack_member list

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
(*s Lazy reduction. *)

(* [fconstr] is the type of frozen constr *)

type fconstr

(* [fconstr] can be accessed by using the function [fterm_of] and by
   matching on type [fterm] *)

type fterm =
  | FRel of int
  | FAtom of constr
  | FCast of fconstr * fconstr
  | FFlex of table_key
  | FInd of inductive
  | FConstruct of constructor
  | FApp of fconstr * fconstr array
  | FFix of (int array * int) * (name array * fconstr array * fconstr array)
      * constr array * fconstr subs
  | FCoFix of int * (name array * fconstr array * fconstr array)
      * constr array * fconstr subs
  | FCases of case_info * fconstr * fconstr * fconstr array
  | FLambda of name * fconstr * fconstr * constr * fconstr subs
  | FProd of name * fconstr * fconstr * constr * fconstr subs
  | FLetIn of name * fconstr * fconstr * fconstr * constr * fconstr subs
  | FEvar of existential_key * fconstr array
  | FLIFT of int * fconstr
  | FCLOS of constr * fconstr subs
  | FLOCKED


(* To lazy reduce a constr, create a ['a clos_infos] with
   [create_cbv_infos], inject the term to reduce with [inject]; then use
   a reduction function *)

val inject : constr -> fconstr
val fterm_of : fconstr -> fterm
val term_of_fconstr : fconstr -> constr

(* Global and local constant cache *)
type clos_infos
val create_clos_infos : flags -> env -> clos_infos

(* Reduction function *)

(* [norm_val] is for strong normalization *)
val norm_val : clos_infos -> fconstr -> constr

(* [whd_val] is for weak head normalization *)
val whd_val : clos_infos -> fconstr -> constr

(* Conversion auxiliary functions to do step by step normalisation *)

(* [fhnf] and [fnf_apply] are for weak head normalization but staying
   in [fconstr] world to perform step by step weak head normalization *)

val fhnf: clos_infos -> fconstr -> int * fconstr * fconstr stack
val fhnf_apply : clos_infos ->
  int -> fconstr -> fconstr stack -> int * fconstr * fconstr stack

(* [unfold_reference] unfolds references in a [fconstr] *)
val unfold_reference : clos_infos -> table_key -> fconstr option

(***********************************************************************)
(*i This is for lazy debug *)

val lift_fconstr : int -> fconstr -> fconstr
val lift_fconstr_vect : int -> fconstr array -> fconstr array

val mk_clos : fconstr subs -> constr -> fconstr
val mk_clos_vect : fconstr subs -> constr array -> fconstr array
val mk_clos_deep :
  (fconstr subs -> constr -> fconstr) ->
   fconstr subs -> constr -> fconstr

val knr: clos_infos -> fconstr -> fconstr stack ->
  fconstr * fconstr stack
val kl: clos_infos -> fconstr -> fconstr

val to_constr :
  (lift -> fconstr -> constr) -> lift -> fconstr -> constr

(* End of cbn debug section i*)
