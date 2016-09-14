(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

Require Import ZArith.
Require Import Coq.Arith.Max.
Require Import List.
Set Implicit Arguments.

(* 
 * This adds a Leaf constructor to the varmap data structure (plugins/quote/Quote.v)
 * --- it is harmless and spares a lot of Empty.
 * It also means smaller proof-terms.
 * As a side note, by dropping the polymorphism, one gets small, yet noticeable, speed-up.
 *)

Section MakeVarMap.
  
  Variable A : Type.
  Variable default : A.

  Inductive t  : Type :=
  | Empty : t
  | Leaf : A -> t
  | Node : t  -> A -> t  -> t .

  Fixpoint find (vm : t) (p:positive) {struct vm} : A :=
    match vm with
      | Empty => default
      | Leaf i => i
      | Node l e r => match p with
                        | xH => e
                        | xO p => find l p
                        | xI p => find r p
                      end
    end.


  Fixpoint singleton (x:positive) (v : A) : t :=
    match x with
    | xH => Leaf v
    | xO p => Node (singleton p v) default Empty
    | xI p => Node Empty default (singleton p v)
    end.
  
  Fixpoint vm_add (x: positive) (v : A) (m : t) {struct m} : t :=
    match m with
    | Empty   => singleton x v
    | Leaf vl =>
      match x with
      | xH => Leaf v
      | xO p => Node (singleton p v) vl Empty
      | xI p => Node Empty vl (singleton p v)
      end
    | Node l o r => 
      match x with
      | xH => Node l v r
      | xI p => Node l o (vm_add p v r)
      | xO p => Node (vm_add p v l) o r
      end
    end.

  
End MakeVarMap.  
