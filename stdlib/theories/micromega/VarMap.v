(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

Require Import BinInt.
Require Import List.
Set Implicit Arguments.

(*
 * This adds a Leaf constructor to the varmap data structure (plugins/quote/Quote.v)
 * --- it is harmless and spares a lot of Empty.
 * It also means smaller proof-terms.
 * As a side note, by dropping the polymorphism, one gets small, yet noticeable, speed-up.
 *)

Inductive t {A} : Type :=
| Empty : t
| Elt : A -> t
| Branch : t  -> A -> t  -> t .
Arguments t : clear implicits.

Register Branch as micromega.VarMap.Branch.
Register Elt    as micromega.VarMap.Elt.
Register Empty  as micromega.VarMap.Empty.
Register t      as micromega.VarMap.type.

Section MakeVarMap.

  Variable A : Type.
  Variable default : A.

  Notation t := (t A).

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

(* TODO #14736 for compatibility only, should be removed after deprecation *)
