(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Reals ZArith.
Require Export GroebnerR.

Open Scope Z_scope.

Lemma groebnerZhypR: forall x y:Z, x=y -> IZR x = IZR y.
Admitted.

Lemma groebnerZconclR: forall x y:Z, IZR x = IZR y -> x = y.
Admitted.

Lemma groebnerZhypnotR: forall x y:Z, x<>y -> IZR x <> IZR y.
Admitted.

Lemma groebnerZconclnotR: forall x y:Z, IZR x <> IZR y -> x <> y.
Admitted.

Ltac groebnerZversR1 :=
 repeat 
  (match goal with
   | H:(@eq Z ?x ?y) |- _ =>
       generalize (@groebnerZhypR _ _ H); clear H; intro H
   | |- (@eq Z ?x ?y) => apply groebnerZconclR
   | H:not (@eq Z ?x ?y) |- _ =>
       generalize (@groebnerZhypnotR _ _ H); clear H; intro H
   | |- not (@eq Z ?x ?y) => apply groebnerZconclnotR
   end).

Lemma groebnerZR1: forall x y:Z, IZR(x+y) = (IZR x + IZR y)%R.
Admitted.
Lemma groebnerZR2: forall x y:Z, IZR(x*y) = (IZR x * IZR y)%R.
Admitted.
Lemma groebnerZR3: forall x y:Z, IZR(x-y) = (IZR x - IZR y)%R.
Admitted.
Lemma groebnerZR4: forall (x:Z) p, IZR(x ^ Zpos p) = (IZR x ^ nat_of_P p)%R.
Admitted.
Ltac groebnerZversR2:=
  repeat
   (rewrite groebnerZR1 in * ||
    rewrite groebnerZR2 in * ||
    rewrite groebnerZR3 in * ||
    rewrite groebnerZR4 in *).

Ltac groebnerZ_begin :=
 intros;
 groebnerZversR1;
 groebnerZversR2;
 simpl in *.
 (*cbv beta iota zeta delta [nat_of_P Pmult_nat plus mult] in *.*)

Ltac groebnerZ := 
 groebnerZ_begin; (*idtac "groebnerZ_begin;";*)
 groebnerR.
