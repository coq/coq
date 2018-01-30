(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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
  | Levar         of Evar.t * lambda (* type *) * lambda array (* arguments *)
  | Lprod         of lambda * lambda 
  | Llam          of Name.t array * lambda  
  | Llet          of Name.t * lambda * lambda
  | Lapp          of lambda * lambda array
  | Lconst        of prefix * pconstant
  | Lproj         of prefix * Constant.t (* prefix, projection name *)
  | Lprim         of prefix * Constant.t * CPrimitives.t * lambda array
  | Lcase         of annot_sw * lambda * lambda * lam_branches 
                  (* annotations, term being matched, accu, branches *)
  | Lif           of lambda * lambda * lambda
  | Lfix          of (int array * int) * fix_decl 
  | Lcofix        of int * fix_decl 
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

and lam_branches = (constructor * Name.t array * lambda) array 

and fix_decl =  Name.t array * lambda array * lambda array
