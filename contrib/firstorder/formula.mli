(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Term
open Names
open Libnames

val qflag : bool ref

val red_flags: Closure.RedFlags.reds ref

val (=?) : ('a -> 'a -> int) -> ('b -> 'b -> int) -> 
  'a -> 'a -> 'b -> 'b -> int
  
val (==?) : ('a -> 'a -> 'b ->'b -> int) -> ('c -> 'c -> int) -> 
  'a -> 'a -> 'b -> 'b -> 'c ->'c -> int

type ('a,'b) sum = Left of 'a | Right of 'b

type counter = bool -> metavariable

val construct_nhyps : inductive -> Proof_type.goal Tacmach.sigma -> int array

val ind_hyps : int -> inductive -> constr list -> 
  Proof_type.goal Tacmach.sigma -> rel_context array

type atoms = {positive:constr list;negative:constr list}

type side = Hyp | Concl | Hint

val dummy_id: global_reference
			
val build_atoms : Proof_type.goal Tacmach.sigma -> counter -> 
  side -> constr -> bool * atoms

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

val build_formula : side -> global_reference -> types -> 
  Proof_type.goal Tacmach.sigma -> counter -> (t,types) sum

