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
open Nativevalues

(** This file defines the lambda code for the native compiler. It has been
extracted from Nativelambda.ml because of the retroknowledge architecture. *)

type prefix = string

type uint =
  | UintVal of Uint31.t
  | UintDigits of prefix * constructor * lambda array
  | UintDecomp of prefix * constructor * lambda

and lambda =
  | Lrel          of Name.t * int 
  | Lvar          of Id.t
  | Lmeta         of metavariable * lambda (* type *)
  | Levar         of Evar.t * lambda array (* arguments *)
  | Lprod         of lambda * lambda 
  | Llam          of Name.t array * lambda  
  | Llet          of Name.t * lambda * lambda
  | Lapp          of lambda * lambda array
  | Lconst        of prefix * pconstant
  | Lproj         of prefix * inductive * int (* prefix, inductive, index starting from 0 *)
  | Lprim         of prefix * Constant.t * CPrimitives.t * lambda array
  | Lcase         of annot_sw * lambda * lambda * lam_branches 
                  (* annotations, term being matched, accu, branches *)
  | Lif           of lambda * lambda * lambda
  | Lfix          of (int array * (string * inductive) array * int) * fix_decl
  | Lcofix        of int * fix_decl (* must be in eta-expanded form *)
  | Lmakeblock    of prefix * pconstructor * int * lambda array
                  (* prefix, constructor name, constructor tag, arguments *)
	(* A fully applied constructor *)
  | Lconstruct    of prefix * pconstructor
	(* A partially applied constructor *)
  | Luint         of uint
  | Lval          of Nativevalues.t
  | Lsort         of Sorts.t
  | Lind          of prefix * pinductive
  | Llazy
  | Lforce

(* Cofixpoints have to be in eta-expanded form for their call-by-need evaluation
to be correct. Otherwise, memoization of previous evaluations will be applied
again to extra arguments (see #7333). *)

and lam_branches = (constructor * Name.t array * lambda) array 

and fix_decl =  Name.t array * lambda array * lambda array
