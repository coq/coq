(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
open Nativevalues

(** This file defines the lambda code generation phase of the native compiler *)
type prefix = string

type case_annot = case_info * reloc_table * Declarations.recursivity_kind

type lambda =
  | Lrel          of Name.t * int
  | Lvar          of Id.t
  | Lmeta         of metavariable * lambda (* type *)
  | Levar         of Evar.t * lambda array (* arguments *)
  | Lprod         of lambda * lambda
  | Llam          of Name.t Context.binder_annot array * lambda
  | Llet          of Name.t Context.binder_annot * lambda * lambda
  | Lapp          of lambda * lambda array
  | Lconst        of pconstant
  | Lproj         of Projection.Repr.t * lambda
  | Lprim         of pconstant * CPrimitives.t * lambda array
  | Lcase         of case_annot * lambda * lambda * lam_branches
                  (* annotations, term being matched, accu, branches *)
  | Lfix          of (int array * inductive array * int) * fix_decl
  | Lcofix        of int * fix_decl
  | Lint          of int (* a constant constructor *)
  | Lparray       of lambda array * lambda
  | Lmakeblock    of inductive * int * lambda array
                  (* inductive name, constructor tag, arguments *)
        (* A fully applied non-constant constructor *)
  | Luint         of Uint63.t
  | Lfloat        of Float64.t
  | Lval          of Nativevalues.t
  | Lsort         of Sorts.t
  | Lind          of pinductive
  | Lforce

and lam_branches =
  { constant_branches : lambda array;
    nonconstant_branches : (Name.t Context.binder_annot array * lambda) array;
  }

and fix_decl =  Name.t Context.binder_annot array * lambda array * lambda array

type evars =
    { evars_val : constr evar_handler;
      evars_metas : metavariable -> types }

val empty_evars : evars

val decompose_Llam : lambda -> Name.t Context.binder_annot array * lambda
val decompose_Llam_Llet : lambda -> (Name.t Context.binder_annot * lambda option) array * lambda

val is_lazy : constr -> bool

val get_mind_prefix : env -> MutInd.t -> string
val get_const_prefix : env -> Constant.t -> string

val get_alias : env -> pconstant -> pconstant

val lambda_of_constr : env -> evars -> Constr.constr -> lambda
