(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
open Names
open Term
open Nativevalues

(** This file defines the lambda code for the native compiler. It has been
extracted from Nativelambda.ml because of the retroknowledge architecture. *)

type prefix = string

type uint =
  | UintVal of Uint31.t
  | UintDigits of prefix * constructor * lambda array
  | UintDecomp of prefix * constructor * lambda

and lambda =
  | Lrel          of name * int 
  | Lvar          of identifier
  | Lmeta         of metavariable * lambda (* type *)
  | Levar         of existential * lambda (* type *)
  | Lprod         of lambda * lambda 
  | Llam          of name array * lambda  
  | Llet          of name * lambda * lambda
  | Lapp          of lambda * lambda array
  | Lconst        of prefix * constant
  | Lprim         of prefix * constant * Primitives.t * lambda array
  | Lcase         of annot_sw * lambda * lambda * lam_branches 
                  (* annotations, term being matched, accu, branches *)
  | Lif           of lambda * lambda * lambda
  | Lfix          of (int array * int) * fix_decl 
  | Lcofix        of int * fix_decl 
  | Lmakeblock    of prefix * constructor * int * lambda array
                  (* prefix, constructor name, constructor tag, arguments *)
	(* A fully applied constructor *)
  | Lconstruct    of prefix * constructor
	(* A partially applied constructor *)
  | Luint         of uint
  | Lval          of Nativevalues.t
  | Lsort         of sorts
  | Lind          of prefix * inductive
  | Llazy
  | Lforce

and lam_branches = (constructor * name array * lambda) array 

and fix_decl =  name array * lambda array * lambda array
