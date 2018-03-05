(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(****************************************************************************)
(*                                                                          *)
(*                         Naive Set Theory in Coq                          *)
(*                                                                          *)
(*                     INRIA                        INRIA                   *)
(*              Rocquencourt                        Sophia-Antipolis        *)
(*                                                                          *)
(*                                 Coq V6.1                                 *)
(*									    *)
(*			         Gilles Kahn 				    *)
(*				 Gerard Huet				    *)
(*									    *)
(*									    *)
(*                                                                          *)
(* Acknowledgments: This work was started in July 1993 by F. Prost. Thanks  *)
(* to the Newton Institute for providing an exceptional work environment    *)
(* in Summer 1995. Several developments by E. Ledinot were an inspiration.  *)
(****************************************************************************)

Require Export Relations_1.
Require Export Relations_1_facts.
Require Export Relations_2.
Require Export Relations_2_facts.
Require Export Relations_3.

Theorem Rstar_imp_coherent :
 forall (U:Type) (R:Relation U) (x y:U), Rstar U R x y -> coherent U R x y.
Proof.
intros U R x y H'; red.
exists y; auto with sets.
Qed.
Hint Resolve Rstar_imp_coherent.

Theorem coherent_symmetric :
 forall (U:Type) (R:Relation U), Symmetric U (coherent U R).
Proof.
unfold coherent at 1.
intros U R; red.
intros x y H'; elim H'.
intros z H'0; exists z; tauto.
Qed.

Theorem Strong_confluence :
 forall (U:Type) (R:Relation U), Strongly_confluent U R -> Confluent U R.
Proof.
intros U R H'; red.
intro x; red; intros a b H'0.
unfold coherent at 1.
generalize b; clear b.
elim H'0; clear H'0.
intros x0 b H'1; exists b; auto with sets.
intros x0 y z H'1 H'2 H'3 b H'4.
generalize (Lemma1 U R); intro h; lapply h;
 [ intro H'0; generalize (H'0 x0 b); intro h0; lapply h0;
    [ intro H'5; generalize (H'5 y); intro h1; lapply h1;
       [ intro h2; elim h2; intros z0 h3; elim h3; intros H'6 H'7;
          clear h h0 h1 h2 h3
       | clear h h0 h1 ]
    | clear h h0 ]
 | clear h ]; auto with sets.
generalize (H'3 z0); intro h; lapply h;
 [ intro h0; elim h0; intros z1 h1; elim h1; intros H'8 H'9; clear h h0 h1
 | clear h ]; auto with sets.
exists z1; split; auto with sets.
apply Rstar_n with z0; auto with sets.
Qed.

Theorem Strong_confluence_direct :
 forall (U:Type) (R:Relation U), Strongly_confluent U R -> Confluent U R.
Proof.
intros U R H'; red.
intro x; red; intros a b H'0.
unfold coherent at 1.
generalize b; clear b.
elim H'0; clear H'0.
intros x0 b H'1; exists b; auto with sets.
intros x0 y z H'1 H'2 H'3 b H'4.
cut (ex (fun t:U => Rstar U R y t /\ R b t)).
intro h; elim h; intros t h0; elim h0; intros H'0 H'5; clear h h0.
generalize (H'3 t); intro h; lapply h;
 [ intro h0; elim h0; intros z0 h1; elim h1; intros H'6 H'7; clear h h0 h1
 | clear h ]; auto with sets.
exists z0; split; [ assumption | idtac ].
apply Rstar_n with t; auto with sets.
generalize H'1; generalize y; clear H'1.
elim H'4.
intros x1 y0 H'0; exists y0; auto with sets.
intros x1 y0 z0 H'0 H'1 H'5 y1 H'6.
red in H'.
generalize (H' x1 y0 y1); intro h; lapply h;
 [ intro H'7; lapply H'7;
    [ intro h0; elim h0; intros z1 h1; elim h1; intros H'8 H'9;
       clear h H'7 h0 h1
    | clear h ]
 | clear h ]; auto with sets.
generalize (H'5 z1); intro h; lapply h;
 [ intro h0; elim h0; intros t h1; elim h1; intros H'7 H'10; clear h h0 h1
 | clear h ]; auto with sets.
exists t; split; auto with sets.
apply Rstar_n with z1; auto with sets.
Qed.

Theorem Noetherian_contains_Noetherian :
 forall (U:Type) (R R':Relation U),
   Noetherian U R -> contains U R R' -> Noetherian U R'.
Proof.
unfold Noetherian at 2.
intros U R R' H' H'0 x.
elim (H' x); auto with sets.
Qed.

Theorem Newman :
 forall (U:Type) (R:Relation U),
   Noetherian U R -> Locally_confluent U R -> Confluent U R.
Proof.
intros U R H' H'0; red; intro x.
elim (H' x); unfold confluent.
intros x0 H'1 H'2 y z H'3 H'4.
generalize (Rstar_cases U R x0 y); intro h; lapply h;
 [ intro h0; elim h0;
    [ clear h h0; intro h1
    | intro h1; elim h1; intros u h2; elim h2; intros H'5 H'6;
       clear h h0 h1 h2 ]
 | clear h ]; auto with sets.
elim h1; auto with sets.
generalize (Rstar_cases U R x0 z); intro h; lapply h;
 [ intro h0; elim h0;
    [ clear h h0; intro h1
    | intro h1; elim h1; intros v h2; elim h2; intros H'7 H'8;
       clear h h0 h1 h2 ]
 | clear h ]; auto with sets.
elim h1; generalize coherent_symmetric; intro t; red in t; auto with sets.
unfold Locally_confluent, locally_confluent, coherent in H'0.
generalize (H'0 x0 u v); intro h; lapply h;
 [ intro H'9; lapply H'9;
    [ intro h0; elim h0; intros t h1; elim h1; intros H'10 H'11;
       clear h H'9 h0 h1
    | clear h ]
 | clear h ]; auto with sets.
clear H'0.
unfold coherent at 1 in H'2.
generalize (H'2 u); intro h; lapply h;
 [ intro H'0; generalize (H'0 y t); intro h0; lapply h0;
    [ intro H'9; lapply H'9;
       [ intro h1; elim h1; intros y1 h2; elim h2; intros H'12 H'13;
          clear h h0 H'9 h1 h2
       | clear h h0 ]
    | clear h h0 ]
 | clear h ]; auto with sets.
generalize Rstar_transitive; intro T; red in T.
generalize (H'2 v); intro h; lapply h;
 [ intro H'9; generalize (H'9 y1 z); intro h0; lapply h0;
    [ intro H'14; lapply H'14;
       [ intro h1; elim h1; intros z1 h2; elim h2; intros H'15 H'16;
          clear h h0 H'14 h1 h2
       | clear h h0 ]
    | clear h h0 ]
 | clear h ]; auto with sets.
red; (exists z1; split); auto with sets.
apply T with y1; auto with sets.
apply T with t; auto with sets.
Qed.
