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
open Libnames

val qflag : bool ref

val (=?) : ('a -> 'a -> int) -> ('b -> 'b -> int) -> 
  'a -> 'a -> 'b -> 'b -> int
  
val (==?) : ('a -> 'a -> 'b ->'b -> int) -> ('c -> 'c -> int) -> 
  'a -> 'a -> 'b -> 'b -> 'c ->'c -> int

type ('a,'b) sum = Left of 'a | Right of 'b

type counter = bool -> metavariable

val construct_nhyps : inductive -> int array

val ind_hyps : int -> inductive -> constr list -> Sign.rel_context array

val match_with_evaluable : Proof_type.goal Tacmach.sigma ->
  constr -> (evaluable_global_reference * constr) option

type kind_of_formula=
    Arrow of constr*constr
  | And of inductive*constr list
  | Or of inductive*constr list
  | Exists of inductive*constr list
  | Forall of constr*constr
  | Atom of constr
  | Evaluable of Names.evaluable_global_reference * Term.constr
  | False

val kind_of_formula : Proof_type.goal Tacmach.sigma -> 
  constr -> kind_of_formula

type atoms = {positive:constr list;negative:constr list}
			
val build_atoms : Proof_type.goal Tacmach.sigma -> counter -> 
  bool -> constr -> bool * atoms

type right_pattern =
    Rand
  | Ror 
  | Rforall
  | Rexists of metavariable*constr*bool
  | Rarrow
  | Revaluable of Names.evaluable_global_reference
    
type right_formula =
    Complex of right_pattern*constr*atoms
  | Atomic of constr
      
type left_arrow_pattern=
    LLatom
  | LLfalse
  | LLand of inductive*constr list
  | LLor of inductive*constr list
  | LLforall of constr
  | LLexists of inductive*constr list
  | LLarrow of constr*constr*constr
  | LLevaluable of Names.evaluable_global_reference

type left_pattern=
    Lfalse    
  | Land of inductive
  | Lor of inductive 
  | Lforall of metavariable*constr*bool
  | Lexists of inductive
  | Levaluable of Names.evaluable_global_reference
  | LA of constr*left_arrow_pattern
      
type left_formula={id:global_reference;
		   constr:constr;
		   pat:left_pattern;
		   atoms:atoms;
		   internal:bool}

(*exception Is_atom of constr*)

val build_left_entry : 
  global_reference -> types -> bool -> Proof_type.goal Tacmach.sigma ->
  counter -> (left_formula,types) sum

val build_right_entry : types -> Proof_type.goal Tacmach.sigma -> 
  counter -> right_formula
