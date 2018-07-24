(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open Names
open Cic
open Esubst
open Environ
(*i*)

(* Flags for profiling reductions. *)
val stats : bool ref
val share : bool ref

val with_stats: 'a Lazy.t -> 'a

(*s Delta implies all consts (both global (= by
  [kernel_name]) and local (= by [Rel] or [Var])), all evars, and letin's.
  Rem: reduction of a Rel/Var bound to a term is Delta, but reduction of
  a LetIn expression is Letin reduction *)

(* Sets of reduction kinds. *)
module type RedFlagsSig = sig
  type reds
  type red_kind

  (* The different kinds of reduction *)
  val fBETA : red_kind
  val fDELTA : red_kind
  val fIOTA : red_kind
  val fZETA : red_kind

  (* No reduction at all *)
  val no_red : reds

  (* Adds a reduction kind to a set *)
  val red_add : reds -> red_kind -> reds

  (* Build a reduction set from scratch = iter [red_add] on [no_red] *)
  val mkflags : red_kind list -> reds

  (* Tests if a reduction kind is set *)
  val red_set : reds -> red_kind -> bool
end

module RedFlags : RedFlagsSig
open RedFlags

val betadeltaiota      : reds
val betaiotazeta       : reds
val betadeltaiotanolet : reds

(***********************************************************************)

type table_key = Constant.t puniverses tableKey

type 'a infos
val ref_value_cache: 'a infos -> table_key -> 'a option
val create: ('a infos -> constr -> 'a) -> reds -> env -> 'a infos

(************************************************************************)
(*s Lazy reduction. *)

(* [fconstr] is the type of frozen constr *)

type fconstr

(* [fconstr] can be accessed by using the function [fterm_of] and by
   matching on type [fterm] *)

type fterm =
  | FRel of int
  | FAtom of constr (* Metas and Sorts *)
  | FCast of fconstr * cast_kind * fconstr
  | FFlex of table_key
  | FInd of pinductive
  | FConstruct of pconstructor
  | FApp of fconstr * fconstr array
  | FProj of Projection.t * fconstr
  | FFix of fixpoint * fconstr subs
  | FCoFix of cofixpoint * fconstr subs
  | FCaseT of case_info * constr * fconstr * constr array * fconstr subs (* predicate and branches are closures *)
  | FLambda of int * (Name.t * constr) list * constr * fconstr subs
  | FProd of Name.t * fconstr * fconstr
  | FLetIn of Name.t * fconstr * fconstr * constr * fconstr subs
  | FEvar of existential_key * fconstr array
  | FLIFT of int * fconstr
  | FCLOS of constr * fconstr subs
  | FLOCKED

(************************************************************************)
(*s A [stack] is a context of arguments, arguments are pushed by
   [append_stack] one array at a time but popped with [decomp_stack]
   one by one *)

type stack_member =
  | Zapp of fconstr array
  | ZcaseT of case_info * constr * constr array * fconstr subs
  | Zproj of Projection.Repr.t
  | Zfix of fconstr * stack
  | Zshift of int
  | Zupdate of fconstr

and stack = stack_member list

val append_stack : fconstr array -> stack -> stack

val stack_args_size : stack -> int
    
val eta_expand_stack : stack -> stack
 
val eta_expand_ind_stack : env -> inductive -> fconstr -> stack -> 
   (fconstr * stack) -> stack * stack

val unfold_projection : env -> Projection.t -> stack_member

(* To lazy reduce a constr, create a [clos_infos] with
   [create_clos_infos], inject the term to reduce with [inject]; then use
   a reduction function *)

val inject : constr -> fconstr

val fterm_of : fconstr -> fterm
val term_of_fconstr : fconstr -> constr
val destFLambda :
  (fconstr subs -> constr -> fconstr) -> fconstr -> Name.t * fconstr * fconstr

(* Global and local constant cache *)
type clos_infos
val create_clos_infos : reds -> env -> clos_infos
val infos_env : clos_infos -> env
val infos_flags : clos_infos -> reds
val oracle_of_infos : clos_infos -> oracle


(* Reduction function *)

(* [whd_val] is for weak head normalization *)
val whd_val : clos_infos -> fconstr -> constr

(* [whd_stack] performs weak head normalization in a given stack. It
   stops whenever a reduction is blocked. *)
val whd_stack :
  clos_infos -> fconstr -> stack -> fconstr * stack

(* Conversion auxiliary functions to do step by step normalisation *)

(* [unfold_reference] unfolds references in a [fconstr] *)
val unfold_reference : clos_infos -> table_key -> fconstr option

(* [mind_equiv] checks whether two inductive types are intentionally equal *)
val mind_equiv_infos : clos_infos -> inductive -> inductive -> bool

(************************************************************************)
(*i This is for lazy debug *)

val lift_fconstr      : int -> fconstr -> fconstr
val lift_fconstr_vect : int -> fconstr array -> fconstr array

val mk_clos      : fconstr subs -> constr -> fconstr
val mk_clos_vect : fconstr subs -> constr array -> fconstr array
val mk_clos_deep :
  (fconstr subs -> constr -> fconstr) ->
   fconstr subs -> constr -> fconstr

val kni: clos_infos -> fconstr -> stack -> fconstr * stack
val knr: clos_infos -> fconstr -> stack -> fconstr * stack

val to_constr : (lift -> fconstr -> constr) -> lift -> fconstr -> constr

(* End of cbn debug section i*)
