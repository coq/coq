(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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

  #[universes(template)]
  Inductive t  : Type :=
  | Empty : t
  | Elt : A -> t
  | Branch : t  -> A -> t  -> t .

  Fixpoint find (vm : t) (p:positive) {struct vm} : A :=
    match vm with
      | Empty => default
      | Elt i => i
      | Branch l e r => match p with
                        | xH => e
                        | xO p => find l p
                        | xI p => find r p
                      end
    end.


  Fixpoint singleton (x:positive) (v : A) : t :=
    match x with
    | xH => Elt v
    | xO p => Branch (singleton p v) default Empty
    | xI p => Branch Empty default (singleton p v)
    end.
  
  Fixpoint vm_add (x: positive) (v : A) (m : t) {struct m} : t :=
    match m with
    | Empty   => singleton x v
    | Elt vl =>
      match x with
      | xH => Elt v
      | xO p => Branch (singleton p v) vl Empty
      | xI p => Branch Empty vl (singleton p v)
      end
    | Branch l o r =>
      match x with
      | xH => Branch l v r
      | xI p => Branch l o (vm_add p v r)
      | xO p => Branch (vm_add p v l) o r
      end
    end.

  
End MakeVarMap.  
