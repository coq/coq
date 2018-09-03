(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Environ
open Esubst

(** Flags for profiling reductions. *)
val stats : bool ref

val with_stats: 'a Lazy.t -> 'a

(** {6 ... } *)
(** Delta implies all consts (both global (= by
  [kernel_name]) and local (= by [Rel] or [Var])), all evars, and letin's.
  Rem: reduction of a Rel/Var bound to a term is Delta, but reduction of
  a LetIn expression is Letin reduction *)



val all_opaque      : transparent_state
val all_transparent : transparent_state

val is_transparent_variable : transparent_state -> variable -> bool
val is_transparent_constant : transparent_state -> Constant.t -> bool

(** Sets of reduction kinds. *)
module type RedFlagsSig = sig
  type reds
  type red_kind

  (** {7 The different kinds of reduction } *)

  val fBETA : red_kind
  val fDELTA : red_kind
  val fETA : red_kind
  (** The fETA flag is never used by the kernel reduction but pretyping does *)
  val fMATCH : red_kind
  val fFIX : red_kind
  val fCOFIX : red_kind
  val fZETA : red_kind
  val fCONST : Constant.t -> red_kind
  val fVAR : Id.t -> red_kind

  (** No reduction at all *)
  val no_red : reds

  (** Adds a reduction kind to a set *)
  val red_add : reds -> red_kind -> reds

  (** Removes a reduction kind to a set *)
  val red_sub : reds -> red_kind -> reds

  (** Adds a reduction kind to a set *)
  val red_add_transparent : reds -> transparent_state -> reds

  (** Retrieve the transparent state of the reduction flags *)
  val red_transparent : reds -> transparent_state

  (** Build a reduction set from scratch = iter [red_add] on [no_red] *)
  val mkflags : red_kind list -> reds

  (** Tests if a reduction kind is set *)
  val red_set : reds -> red_kind -> bool

  (** This tests if the projection is in unfolded state already or
      is unfodable due to delta. *)
  val red_projection : reds -> Projection.t -> bool
end

module RedFlags : RedFlagsSig
open RedFlags

(* These flags do not contain eta *)
val all               : reds
val allnolet          : reds
val beta              : reds
val betadeltazeta     : reds
val betaiota          : reds
val betaiotazeta      : reds
val betazeta          : reds
val delta             : reds
val zeta              : reds
val nored             : reds


val unfold_side_red : reds
val unfold_red : evaluable_global_reference -> reds

(***********************************************************************)
type table_key = Constant.t Univ.puniverses tableKey

type 'a infos_cache
type 'a infos_tab
type 'a infos = {
  i_flags : reds;
  i_cache : 'a infos_cache }

val ref_value_cache: 'a infos -> 'a infos_tab -> table_key -> 'a option
val create:
  repr:('a infos -> 'a infos_tab -> constr -> 'a) ->
  share:bool ->
  reds ->
  env ->
  (existential -> constr option) ->
  'a infos
val create_tab : unit -> 'a infos_tab
val evar_value : 'a infos_cache -> existential -> constr option

val info_env : 'a infos -> env
val info_flags: 'a infos -> reds

(***********************************************************************
  s Lazy reduction. *)

(** [fconstr] is the type of frozen constr *)

type fconstr

(** [fconstr] can be accessed by using the function [fterm_of] and by
   matching on type [fterm] *)

type fterm =
  | FRel of int
  | FAtom of constr (** Metas and Sorts *)
  | FCast of fconstr * cast_kind * fconstr
  | FFlex of table_key
  | FInd of inductive Univ.puniverses
  | FConstruct of constructor Univ.puniverses
  | FApp of fconstr * fconstr array
  | FProj of Projection.t * fconstr
  | FFix of fixpoint * fconstr subs
  | FCoFix of cofixpoint * fconstr subs
  | FCaseT of case_info * constr * fconstr * constr array * fconstr subs (* predicate and branches are closures *)
  | FLambda of int * (Name.t * constr) list * constr * fconstr subs
  | FProd of Name.t * fconstr * fconstr
  | FLetIn of Name.t * fconstr * fconstr * constr * fconstr subs
  | FEvar of existential * fconstr subs
  | FLIFT of int * fconstr
  | FCLOS of constr * fconstr subs
  | FLOCKED

(***********************************************************************
  s A [stack] is a context of arguments, arguments are pushed by
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

val empty_stack : stack
val append_stack : fconstr array -> stack -> stack

val decomp_stack : stack -> (fconstr * stack) option
val array_of_stack : stack -> fconstr array
val stack_assign : stack -> int -> fconstr -> stack
val stack_args_size : stack -> int
val stack_tail : int -> stack -> stack
val stack_nth : stack -> int -> fconstr
val zip_term : (fconstr -> constr) -> constr -> stack -> constr
val eta_expand_stack : stack -> stack
val unfold_projection : 'a infos -> Projection.t -> stack_member option

(** To lazy reduce a constr, create a [clos_infos] with
   [create_clos_infos], inject the term to reduce with [inject]; then use
   a reduction function *)

val inject : constr -> fconstr

(** mk_atom: prevents a term from being evaluated *)
val mk_atom : constr -> fconstr

(** mk_red: makes a reducible term (used in newring) *)
val mk_red : fterm -> fconstr

val fterm_of : fconstr -> fterm
val term_of_fconstr : fconstr -> constr
val destFLambda :
  (fconstr subs -> constr -> fconstr) -> fconstr -> Name.t * fconstr * fconstr

(** Global and local constant cache *)
type clos_infos = fconstr infos
val create_clos_infos :
  ?evars:(existential->constr option) -> reds -> env -> clos_infos
val oracle_of_infos : clos_infos -> Conv_oracle.oracle

val env_of_infos : 'a infos -> env

val infos_with_reds : clos_infos -> reds -> clos_infos

(** Reduction function *)

(** [norm_val] is for strong normalization *)
val norm_val : clos_infos -> fconstr infos_tab -> fconstr -> constr

(** [whd_val] is for weak head normalization *)
val whd_val : clos_infos -> fconstr infos_tab -> fconstr -> constr

(** [whd_stack] performs weak head normalization in a given stack. It
   stops whenever a reduction is blocked. *)
val whd_stack :
  clos_infos -> fconstr infos_tab -> fconstr -> stack -> fconstr * stack

(** [eta_expand_ind_stack env ind c s t] computes stacks correspoding
    to the conversion of the eta expansion of t, considered as an inhabitant
    of ind, and the Constructor c of this inductive type applied to arguments
    s.
    @assumes [t] is a rigid term, and not a constructor. [ind] is the inductive
    of the constructor term [c]
    @raise Not_found if the inductive is not a primitive record, or if the
    constructor is partially applied.
 *)
val eta_expand_ind_stack : env -> inductive -> fconstr -> stack ->
   (fconstr * stack) -> stack * stack

(** Conversion auxiliary functions to do step by step normalisation *)

(** [unfold_reference] unfolds references in a [fconstr] *)
val unfold_reference : clos_infos -> fconstr infos_tab -> table_key -> fconstr option

val eq_table_key : table_key -> table_key -> bool

(***********************************************************************
  i This is for lazy debug *)

val lift_fconstr      : int -> fconstr -> fconstr
val lift_fconstr_vect : int -> fconstr array -> fconstr array

val mk_clos      : fconstr subs -> constr -> fconstr
val mk_clos_vect : fconstr subs -> constr array -> fconstr array

val kni: clos_infos -> fconstr infos_tab -> fconstr -> stack -> fconstr * stack
val knr: clos_infos -> fconstr infos_tab -> fconstr -> stack -> fconstr * stack
val kl : clos_infos -> fconstr infos_tab -> fconstr -> constr

val to_constr : lift -> fconstr -> constr

(** End of cbn debug section i*)
