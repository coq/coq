(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Term
open Names

type ('a,'b) sum = Left of 'a | Right of 'b

type kind_of_formula=
   Arrow of constr*constr
  |And of inductive*constr list
  |Or of inductive*constr list
  |Exists of inductive*constr*constr*constr
  |Forall of constr*constr
  |Atom of constr
  |False

type counter = bool -> int

val newcnt : unit -> counter

val construct_nhyps : inductive -> int array
      
val ind_hyps : inductive -> constr list -> Sign.rel_context array

val kind_of_formula : constr -> kind_of_formula
			
type right_pattern =
    Rand
  | Ror 
  | Rforall
  | Rexists of int*constr
  | Rarrow
      
type right_formula =
    Complex of right_pattern*((bool*constr) list)
  | Atomic of constr
      
type left_pattern=
    Lfalse    
  | Land of inductive
  | Lor of inductive 
  | Lforall of int*constr
  | Lexists
  | LAatom of constr
  | LAfalse
  | LAand of inductive*constr list
  | LAor of inductive*constr list
  | LAforall of constr
  | LAexists of inductive*constr*constr*constr
  | LAarrow of constr*constr*constr
      
type left_formula={id:identifier;
		   pat:left_pattern;
		   atoms:(bool*constr) list}

val build_left_entry : 
  identifier -> types -> counter -> (left_formula,types) sum

val build_right_entry : types -> counter -> right_formula


