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

type kind_of_formula =
    Arrow of constr*constr
  | False of inductive*constr list
  | And of inductive*constr list
  | Or of inductive*constr list
  | Exists of inductive*constr list
  | Forall of constr*constr
  | Atom of constr

val kind_of_formula : Proof_type.goal Tacmach.sigma -> 
  constr -> kind_of_formula

type atoms = {positive:constr list;negative:constr list}

val dummy_id: global_reference
			
val build_atoms : Proof_type.goal Tacmach.sigma -> counter -> 
  bool -> constr -> bool * atoms

type right_pattern =
    Rarrow
  | Rand
  | Ror 
  | Rfalse
  | Rforall
  | Rexists of metavariable*constr*bool
    
type left_arrow_pattern=
    LLatom
  | LLfalse of inductive*constr list
  | LLand of inductive*constr list
  | LLor of inductive*constr list
  | LLforall of constr
  | LLexists of inductive*constr list
  | LLarrow of constr*constr*constr

type left_pattern=
    Lfalse    
  | Land of inductive
  | Lor of inductive 
  | Lforall of metavariable*constr*bool
  | Lexists of inductive
  | LA of constr*left_arrow_pattern
      
type t={id: global_reference;
	constr: constr;
	pat: (left_pattern,right_pattern) sum;
	atoms: atoms}
    
(*exception Is_atom of constr*)

val build_formula : bool -> global_reference -> types -> 
  Proof_type.goal Tacmach.sigma -> counter -> (t,types) sum

