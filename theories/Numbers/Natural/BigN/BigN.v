(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** * Natural numbers in base 2^31 *)

(**
Author: Arnaud Spiwack
*)

Require Export Int31.
Require Import Z31Z.
Require Import NMake.
Require Import ZnZ.

Open Scope int31_scope.

Module BigN := NMake.Make Int31_words.

Definition bigN := BigN.t.

Delimit Scope bigN_scope with bigN.
Bind Scope bigN_scope with bigN.
Bind Scope bigN_scope with BigN.t.
Bind Scope bigN_scope with BigN.t_.

Notation " i + j " := (BigN.add i j) : bigN_scope.
Notation " i - j " := (BigN.sub i j) : bigN_scope.
Notation " i * j " := (BigN.mul i j) : bigN_scope.
Notation " i / j " := (BigN.div i j) : bigN_scope.
Notation " i ?= j " := (BigN.compare i j) : bigN_scope.

 Theorem succ_pred: forall q,
  (0 < BigN.to_Z q -> 
     BigN.to_Z (BigN.succ (BigN.pred q)) = BigN.to_Z q)%Z.
 intros q Hq.
 rewrite BigN.spec_succ.
 rewrite BigN.spec_pred; auto.
 generalize Hq; set (a := BigN.to_Z q).
 ring_simplify (a - 1 + 1)%Z; auto.
 Qed.
 
