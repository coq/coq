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
open Declarations
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
  val red_add_transparent : reds -> TransparentState.t -> reds

  (** Retrieve the transparent state of the reduction flags *)
  val red_transparent : reds -> TransparentState.t

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

module KeyTable : Hashtbl.S with type key = table_key

(***********************************************************************
  s Lazy reduction. *)

(** [fconstr] is the type of frozen constr *)

type fconstr

(** [fconstr] can be accessed by using the function [fterm_of] and by
   matching on type [fterm] *)

type fterm =
  | FRel of int
  | FAtom of constr (** Metas and Sorts *)
  | FFlex of table_key
  | FInd of inductive Univ.puniverses
  | FConstruct of constructor Univ.puniverses
  | FApp of fconstr * fconstr array
  | FProj of Projection.t * fconstr
  | FFix of fixpoint * fconstr subs
  | FCoFix of cofixpoint * fconstr subs
  | FCaseT of case_info * constr * fconstr * constr array * fconstr subs (* predicate and branches are closures *)
  | FLambda of int * (Name.t * constr) list * constr * fconstr subs
  | FProd of Name.t * fconstr * constr * fconstr subs
  | FLetIn of Name.t * fconstr * fconstr * constr * fconstr subs
  | FEvar of existential * fconstr subs
  | FInt of Uint63.t
  | FLIFT of int * fconstr
  | FCLOS of constr * fconstr subs
  | FLOCKED

(***********************************************************************
  s A [stack] is a context of arguments, arguments are pushed by
   [append_stack] one array at a time *)
type 'a next_native_args = (CPrimitives.arg_kind * 'a) list

type stack_member =
  | Zapp of fconstr array
  | ZcaseT of case_info * constr * constr array * fconstr subs
  | Zproj of Projection.Repr.t
  | Zfix of fconstr * stack
  | Zprimitive of CPrimitives.t * pconstant * fconstr list * fconstr next_native_args
       (* operator, constr def, reduced arguments rev, next arguments *)
  | Zshift of int
  | Zupdate of fconstr

and stack = stack_member list

val empty_stack : stack
val append_stack : fconstr array -> stack -> stack

val check_native_args : CPrimitives.t -> stack -> bool
val get_native_args1 : CPrimitives.t -> pconstant -> stack ->
  fconstr list * fconstr * fconstr next_native_args * stack

val stack_args_size : stack -> int
val eta_expand_stack : stack -> stack

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
type clos_infos
type clos_tab
val create_clos_infos :
  ?evars:(existential->constr option) -> reds -> env -> clos_infos
val oracle_of_infos : clos_infos -> Conv_oracle.oracle

val create_tab : unit -> clos_tab

val info_env : clos_infos -> env
val info_flags: clos_infos -> reds
val unfold_projection : clos_infos -> Projection.t -> stack_member option

val infos_with_reds : clos_infos -> reds -> clos_infos

(** Reduction function *)

(** [norm_val] is for strong normalization *)
val norm_val : clos_infos -> clos_tab -> fconstr -> constr

(** [whd_val] is for weak head normalization *)
val whd_val : clos_infos -> clos_tab -> fconstr -> constr

(** [whd_stack] performs weak head normalization in a given stack. It
   stops whenever a reduction is blocked. *)
val whd_stack :
  clos_infos -> clos_tab -> fconstr -> stack -> fconstr * stack

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
val unfold_reference : clos_infos -> clos_tab -> table_key -> fconstr constant_def

(***********************************************************************
  i This is for lazy debug *)

val lift_fconstr      : int -> fconstr -> fconstr
val lift_fconstr_vect : int -> fconstr array -> fconstr array

val mk_clos      : fconstr subs -> constr -> fconstr
val mk_clos_vect : fconstr subs -> constr array -> fconstr array

val kni: clos_infos -> clos_tab -> fconstr -> stack -> fconstr * stack
val knr: clos_infos -> clos_tab -> fconstr -> stack -> fconstr * stack
val kl : clos_infos -> clos_tab -> fconstr -> constr

val to_constr : lift -> fconstr -> constr

(** End of cbn debug section i*)
