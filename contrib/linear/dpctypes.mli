(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ *)

open Names
open Term

type constname =
    ID of identifier
  | SK of identifier
  | CN of constr


type atom_id = constname * int

type term = VAR of identifier 
      	  | GLOB of constname
          | APP of term list

type formula = Atom of atom_id * (term list) 
             | Neg of formula 
             | Imp of formula * formula
             | Conj of formula * formula 
             | Disj of formula * formula
             | ForAll of identifier * formula 
             | Exists of identifier * formula

type sequent = Seq of formula list

type sfla = Po of formula
      	  | No of formula

exception Impossible_case

type lkproof2 = Proof2 of (formula list) * (formula list) * rule2
 and rule2 =
       Axiom2      of formula
     | RWeakening2 of formula * lkproof2
     | LWeakening2 of formula * lkproof2
     | RNeg2       of formula * lkproof2
     | LNeg2       of formula * lkproof2
     | RConj2      of formula * lkproof2 * formula * lkproof2
     | LConj2      of formula * formula * lkproof2
     | RDisj2      of formula * formula * lkproof2
     | LDisj2      of formula * lkproof2 * formula * lkproof2
     | RImp2       of formula * formula * lkproof2
     | LImp2       of formula * lkproof2 * formula * lkproof2
     | RForAll2    of identifier * formula * lkproof2
     | LForAll2    of identifier * term * formula * lkproof2
     | RExists2    of identifier * term * formula * lkproof2
     | LExists2    of identifier * formula * lkproof2

(* $Id$ *)
