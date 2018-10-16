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
open Vmvalues
open Cbytecodes

(** This file defines the lambda code for the bytecode compiler. It has been
extracted from Clambda.ml because of the retroknowledge architecture. *)

type uint =
  | UintVal of Uint31.t
  | UintDigits of lambda array
  | UintDecomp of lambda

and lambda =
  | Lrel          of Name.t * int
  | Lvar          of Id.t
  | Levar         of Evar.t * lambda array
  | Lprod         of lambda * lambda
  | Llam          of Name.t array * lambda
  | Llet          of Name.t * lambda * lambda
  | Lapp          of lambda * lambda array
  | Lconst        of pconstant
  | Lprim         of pconstant * int (* arity *) * instruction * lambda array
  | Lcase         of case_info * reloc_table * lambda * lambda * lam_branches
  | Lfix          of (int array * int) * fix_decl
  | Lcofix        of int * fix_decl (* must be in eta-expanded form *)
  | Lmakeblock    of int * lambda array
  | Lval          of structured_values
  | Lsort         of Sorts.t
  | Lind          of pinductive
  | Lproj         of Projection.Repr.t * lambda
  | Lint          of int
  | Luint         of uint

(* Cofixpoints have to be in eta-expanded form for their call-by-need evaluation
to be correct. Otherwise, memoization of previous evaluations will be applied
again to extra arguments (see #7333). *)

and lam_branches =
  { constant_branches : lambda array;
    nonconstant_branches : (Name.t array * lambda) array }

and fix_decl =  Name.t array * lambda array * lambda array
