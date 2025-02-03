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
open Constr
open Environ
open Esubst
open RedFlags

(** Lazy reduction. *)

(** [fconstr] is the type of frozen constr *)

type fconstr
(** [fconstr] can be accessed by using the function [fterm_of] and by
   matching on type [fterm] *)

type finvert

type evar_repack

type usubs = fconstr subs UVars.puniverses

type table_key = Constant.t UVars.puniverses tableKey

(** Relevances (eg in binder_annot or case_info) have NOT been substituted
    when there is a usubs field *)
type fterm =
  | FRel of int
  | FAtom of constr (** Metas and Sorts *)
  | FFlex of table_key
  | FInd of pinductive
  | FConstruct of pconstructor * fconstr array
  | FApp of fconstr * fconstr array
  | FProj of Projection.t * Sorts.relevance * fconstr
  | FFix of fixpoint * usubs
  | FCoFix of cofixpoint * usubs
  | FCaseT of case_info * UVars.Instance.t * constr array * case_return * fconstr * case_branch array * usubs (* predicate and branches are closures *)
  | FCaseInvert of case_info * UVars.Instance.t * constr array * case_return * finvert * fconstr * case_branch array * usubs
  | FLambda of int * (Name.t binder_annot * constr) list * constr * usubs
  | FProd of Name.t binder_annot * fconstr * constr * usubs
  | FLetIn of Name.t binder_annot * fconstr * fconstr * constr * usubs
  | FEvar of Evar.t * constr list * usubs * evar_repack
  | FInt of Uint63.t
  | FFloat of Float64.t
  | FString of Pstring.t
  | FArray of UVars.Instance.t * fconstr Parray.t * fconstr
  | FLIFT of int * fconstr
  | FCLOS of constr * usubs
  | FIrrelevant
  | FLOCKED

(***********************************************************************
  s A [stack] is a context of arguments, arguments are pushed by
   [append_stack] one array at a time *)
type 'a next_native_args = (CPrimitives.arg_kind * 'a) list

type stack_member =
  | Zapp of fconstr array
  | ZcaseT of case_info * UVars.Instance.t * constr array * case_return * case_branch array * usubs
  | Zproj of Projection.Repr.t * Sorts.relevance
  | Zfix of fconstr * stack
  | Zprimitive of CPrimitives.t * pconstant * fconstr list * fconstr next_native_args
       (* operator, constr def, arguments already seen (in rev order), next arguments *)
  | Zshift of int
  | Zupdate of fconstr

and stack = stack_member list

val empty_stack : stack
val append_stack : fconstr array -> stack -> stack

val check_native_args : CPrimitives.t -> stack -> bool
val get_native_args1 : CPrimitives.t -> pconstant -> stack ->
  fconstr list * fconstr * fconstr next_native_args * stack

val get_invert : finvert -> fconstr array

val stack_args_size : stack -> int

val inductive_subst : Declarations.mutual_inductive_body
  -> UVars.Instance.t
  -> fconstr array
  -> usubs

val usubs_lift : usubs -> usubs
val usubs_liftn : int -> usubs -> usubs
val usubs_cons : fconstr -> usubs -> usubs

(** identity if the first instance is empty *)
val usubst_instance : 'a UVars.puniverses -> UVars.Instance.t -> UVars.Instance.t

val usubst_binder : _ UVars.puniverses -> 'a binder_annot -> 'a binder_annot

(** To lazy reduce a constr, create a [clos_infos] with
   [create_clos_infos], inject the term to reduce with [inject]; then use
   a reduction function *)

val inject : constr -> fconstr

val mk_clos      : usubs -> constr -> fconstr
val mk_clos_vect : usubs -> constr array -> fconstr array

val zip : fconstr -> stack -> fconstr

val fterm_of : fconstr -> fterm
val term_of_fconstr : fconstr -> constr
val term_of_process : fconstr -> stack -> constr
val destFLambda :
  (usubs -> constr -> fconstr) -> fconstr -> Name.t binder_annot * fconstr * fconstr

(** Global and local constant cache *)
type clos_infos
type clos_tab

type 'a evar_expansion =
| EvarDefined of 'a
| EvarUndefined of Evar.t * 'a list

type evar_handler = {
  evar_expand : constr pexistential -> constr evar_expansion;
  evar_repack : Evar.t * constr list -> constr;
  evar_irrelevant : constr pexistential -> bool;
  qvar_irrelevant : Sorts.QVar.t -> bool;
}

val default_evar_handler : env -> evar_handler
val create_conv_infos :
  ?univs:UGraph.t -> ?evars:evar_handler -> reds -> env -> clos_infos
val create_clos_infos :
  ?univs:UGraph.t -> ?evars:evar_handler -> reds -> env -> clos_infos
val oracle_of_infos : clos_infos -> Conv_oracle.oracle

val create_tab : unit -> clos_tab

val info_env : clos_infos -> env
val info_flags: clos_infos -> reds
val info_univs : clos_infos -> UGraph.t
val unfold_projection : clos_infos -> Projection.t -> Sorts.relevance -> stack_member option

val push_relevance : clos_infos -> 'b binder_annot -> clos_infos
val push_relevances : clos_infos -> 'b binder_annot array -> clos_infos
val set_info_relevances : clos_infos -> Sorts.relevance Range.t -> clos_infos

val info_relevances : clos_infos -> Sorts.relevance Range.t

val is_irrelevant : clos_infos -> Sorts.relevance -> bool

val infos_with_reds : clos_infos -> reds -> clos_infos

(** Reduction function *)

(** [norm_val] is for strong normalization *)
val norm_val : clos_infos -> clos_tab -> fconstr -> constr

(** Same as [norm_val] but for terms *)
val norm_term : clos_infos -> clos_tab -> usubs -> Constr.constr -> Constr.constr

(** [whd_val] is for weak head normalization *)
val whd_val : clos_infos -> clos_tab -> fconstr -> constr

(** [whd_stack] performs weak head normalization in a given stack. It
   stops whenever a reduction is blocked. *)
val whd_stack :
  clos_infos -> clos_tab -> fconstr -> stack -> fconstr * stack

val skip_irrelevant_stack : clos_infos -> stack -> stack

val eta_expand_stack : clos_infos -> Name.t binder_annot -> stack -> stack

(** [eta_expand_ind_stack env ind c t] computes stacks corresponding
    to the conversion of the eta expansion of [t], considered as an inhabitant
    of [ind], and the Constructor [c] of this inductive type containing its arguments.
    Assumes [t] is a rigid term, and not a constructor. [ind] is the inductive
    of the constructor term [c].
    @raise Not_found if the inductive is not a primitive record, or if the
    constructor is partially applied.
 *)
val eta_expand_ind_stack : env -> pinductive -> fconstr ->
   (fconstr * stack) -> stack * stack

(** Conversion auxiliary functions to do step by step normalisation *)

(** Like [unfold_reference], but handles primitives: if there are not
    enough arguments, return [None]. Otherwise return [Some] with
    [ZPrimitive] added to the stack. Produces a [FIrrelevant] when the
    reference is irrelevant and the infos was created with
    [create_conv_infos]. *)
val unfold_ref_with_args
  : clos_infos
  -> clos_tab
  -> table_key
  -> stack
  -> (fconstr * stack) option

val get_ref_mask : clos_infos -> clos_tab -> table_key -> bool array

(** Hook for Reduction *)
val set_conv : (clos_infos -> clos_tab -> fconstr -> fconstr -> bool) -> unit
