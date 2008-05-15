(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

(*i $Id$ i*)

Require Export BigN.
Require Import ZMake.


Module BigZ := Make BigN.


Definition bigZ := BigZ.t.

Delimit Scope bigZ_scope with bigZ.
Bind Scope bigZ_scope with bigZ.
Bind Scope bigZ_scope with BigZ.t.
Bind Scope bigZ_scope with BigZ.t_.

Notation " i + j " := (BigZ.add i j) : bigZ_scope.
Notation " i - j " := (BigZ.sub i j) : bigZ_scope.
Notation " i * j " := (BigZ.mul i j) : bigZ_scope.
Notation " i / j " := (BigZ.div i j) : bigZ_scope.
Notation " i ?= j " := (BigZ.compare i j) : bigZ_scope.


 Theorem spec_to_Z: 
  forall n, BigN.to_Z (BigZ.to_N n) = 
            (Zsgn (BigZ.to_Z n) * BigZ.to_Z n)%Z.
 intros n; case n; simpl; intros p; 
     generalize (BigN.spec_pos p); case (BigN.to_Z p); auto.
 intros p1 H1; case H1; auto.
 intros p1 H1; case H1; auto.
 Qed.

 Theorem spec_to_N n: 
  (BigZ.to_Z n = 
    Zsgn (BigZ.to_Z n) * (BigN.to_Z (BigZ.to_N n)))%Z.
 intros n; case n; simpl; intros p; 
     generalize (BigN.spec_pos p); case (BigN.to_Z p); auto.
 intros p1 H1; case H1; auto.
 intros p1 H1; case H1; auto.
 Qed.

 Theorem spec_to_Z_pos: 
  forall n, (0 <= BigZ.to_Z n ->
              BigN.to_Z (BigZ.to_N n) = BigZ.to_Z n)%Z.
 intros n; case n; simpl; intros p; 
     generalize (BigN.spec_pos p); case (BigN.to_Z p); auto.
 intros p1 _  H1; case H1; auto.
 intros p1 H1; case H1; auto.
 Qed.

