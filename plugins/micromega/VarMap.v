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


End MakeVarMap.

