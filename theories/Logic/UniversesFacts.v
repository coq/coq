(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** A proof of the inconsistency of Prop=Type (for some fixed Type) in
    Coq using Hurkens' paradox for system Type:Type [Hurkens].

    Adapted from an initial formulation by Herman Geuvers [Geuvers] (this
    formulation was used to show the inconsistency in the pure
    calculus of constructions of a retract from Prop into a small
    type, see Hurkens.v).

    - [Hurkens] A. J. Hurkens, "A simplification of Girard's paradox",
      Proceedings of the 2nd international conference Typed Lambda-Calculi
      and Applications (TLCA'95), 1995.

    - [Geuvers] "Inconsistency of Classical Logic in Type Theory", 2001
      (see http://www.cs.kun.nl/~herman/note.ps.gz).
*)

Section Paradox.

Definition Type2 := Type.
Definition Type1 := Type : Type2.

(** Preliminary *)

Notation "'rew2' <- H 'in' H'" := (@eq_rect_r Type2 _ (fun X : Type2 => X) H' _ H)
    (at level 10, H' at level 10).
Notation "'rew2' H 'in' H'" := (@eq_rect Type2 _ (fun X : Type2 => X) H' _ H)
    (at level 10, H' at level 10).
Notation "'rew1' <- H 'in' H'" := (@eq_rect_r Type1 _ (fun X : Type1 => X) H' _ H)
    (at level 10, H' at level 10).
Notation "'rew1' H 'in' H'" := (@eq_rect Type1 _ (fun X : Type1 => X) H' _ H)
    (at level 10, H' at level 10).

Lemma rew_rew : forall (A B:Type1) (H:B=A) (x:A), rew1 H in rew1 <- H in x = x.
Proof.
intros.
destruct H.
reflexivity.
Defined. 

(** Main assumption and proof *)

Variable Heq : Prop = Type1 :> Type2.

Definition down : Type1 -> Prop := fun A => rew2 <- Heq in A.
Definition up : Prop -> Type1 := fun A => rew2 Heq in A.

Lemma up_down : forall (A:Type1), up (down A) = A :> Type1.
Proof.
unfold up, down. rewrite Heq. reflexivity.
Defined.

Definition V : Type1 := forall A:Prop, ((up A -> Prop) -> up A -> Prop) -> up A -> Prop.
Definition U : Type1 := V -> Prop.

Definition forth (a:U) : up (down U) := rew1 <- (up_down U) in a.
Definition back (x:up (down U)) : U := rew1 (up_down U) in x. 

Definition sb (z:V) : V := fun A r a => r (z A r) a.
Definition le (i:U -> Prop) (x:U) : Prop := x (fun A r a => i (fun v => sb v A r a)).
Definition le' (i:up (down U) -> Prop) (x:up (down U)) : Prop := le (fun a:U => i (forth a)) (back x).
Definition induct (i:U -> Prop) : Type1 := forall x:U, up (le i x) -> up (i x).
Definition WF : U := fun z => down (induct (fun a => z (down U) le' (forth a))).
Definition I (x:U) : Prop :=
  (forall i:U -> Prop, up (le i x) -> up (i (fun v => sb v (down U) le' (forth x)))) -> False.

Lemma back_forth (a:U) : back (forth a) = a.
Proof.
apply rew_rew.
Defined.

Lemma Omega : forall i:U -> Prop, induct i -> up (i WF).
Proof.
intros i y.
apply y.
unfold le, WF, induct.
rewrite up_down.
intros x H0.
apply y.
unfold sb, le', le.
rewrite back_forth.
exact H0.
Qed.

Lemma lemma1 : induct (fun u => down (I u)).
Proof.
unfold induct.
intros x p.
rewrite up_down.
intro q.
generalize (q (fun u => down (I u)) p).
rewrite up_down.
intro r.
apply r.
intros i j.
unfold le, sb, le', le in j |-.
rewrite back_forth in j.
specialize q with (i := fun y => i (fun v:V => sb v (down U) le' (forth y))).
apply q.
exact j.
Qed.

Lemma lemma2 : (forall i:U -> Prop, induct i -> up (i WF)) -> False.
Proof.
intro x.
generalize (x (fun u => down (I u)) lemma1).
rewrite up_down.
intro r. apply r.
intros i H0.
apply (x (fun y => i (fun v => sb v (down U) le' (forth y)))).
unfold le, WF in H0.
rewrite up_down in H0.
exact H0.
Qed.

Theorem paradox : False.
Proof.
exact (lemma2 Omega).
Qed.

End Paradox.
