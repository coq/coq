(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                              Hurkens.v                               *)
(************************************************************************)

(** Exploiting Hurkens' paradox [[Hurkens95]] for system U- so as to
    derive contradictions from
    - the existence in the pure Calculus of Constructions of a retract
      from Prop into a small type of Prop
    - the existence in the Calculus of Constructions with universes
      of a retract from some Type universe into Prop

    The first proof is a simple and effective formulation by Herman
    Geuvers [[Geuvers01]] of a result by Thierry Coquand
    [[Coquand90]]. The result implies that Coq with classical logic
    stated in impredicative Set is inconsistent and that classical
    logic stated in Prop implies proof-irrelevance (see
    [ClassicalFacts.v])

    The second proof is an adaptation of the first proof by Hugo
    Herbelin to eventually prove the inconsistency of Prop=Type.

    References:

    - [[Coquand90]] T. Coquand, "Metamathematical Investigations of a
      Calculus of Constructions", Proceedings of Logic in Computer
      Science (LICS'90), 1990.

    - [[Hurkens95]] A. J. Hurkens, "A simplification of Girard's paradox",
      Proceedings of the 2nd international conference Typed Lambda-Calculi
      and Applications (TLCA'95), 1995.

    - [[Geuvers01]] H. Geuvers, "Inconsistency of Classical Logic in Type
      Theory", 2001, revised 2007
      (see http://www.cs.ru.nl/~herman/PUBS/newnote.ps.gz).
*)

(* Pleasing coqdoc! *)

(** * Inconsistency of the existence in the pure Calculus of Constructions of a retract from Prop into a small type of Prop *)

Module NoRetractFromSmallPropositionToProp.

Section Paradox.

(** Assumption of a retract from Prop to a small type in Prop, using
    equivalence as the equality on propositions *)

Variable bool : Prop.
Variable p2b : Prop -> bool.
Variable b2p : bool -> Prop.
Hypothesis p2p1 : forall A:Prop, b2p (p2b A) -> A.
Hypothesis p2p2 : forall A:Prop, A -> b2p (p2b A).
Variable B : Prop.

(** Proof *)

Definition V := forall A:Prop, ((A -> bool) -> A -> bool) -> A -> bool.
Definition U := V -> bool.
Definition sb (z:V) : V := fun A r a => r (z A r) a.
Definition le (i:U -> bool) (x:U) : bool :=
  x (fun A r a => i (fun v => sb v A r a)).
Definition induct (i:U -> bool) : Prop :=
  forall x:U, b2p (le i x) -> b2p (i x).
Definition WF : U := fun z => p2b (induct (z U le)).
Definition I (x:U) : Prop :=
  (forall i:U -> bool, b2p (le i x) -> b2p (i (fun v => sb v U le x))) -> B.

Lemma Omega : forall i:U -> bool, induct i -> b2p (i WF).
Proof.
intros i y.
apply y.
unfold le, WF, induct.
apply p2p2.
intros x H0.
apply y.
exact H0.
Qed.

Lemma lemma1 : induct (fun u => p2b (I u)).
Proof.
unfold induct.
intros x p.
apply (p2p2 (I x)).
intro q.
apply (p2p1 (I (fun v:V => sb v U le x)) (q (fun u => p2b (I u)) p)).
intro i.
apply q with (i := fun y => i (fun v:V => sb v U le y)).
Qed.

Lemma lemma2 : (forall i:U -> bool, induct i -> b2p (i WF)) -> B.
Proof.
intro x.
apply (p2p1 (I WF) (x (fun u => p2b (I u)) lemma1)).
intros i H0.
apply (x (fun y => i (fun v => sb v U le y))).
apply (p2p1 _ H0).
Qed.

Theorem paradox : B.
Proof.
exact (lemma2 Omega).
Qed.

End Paradox.

End NoRetractFromSmallPropositionToProp.

Export NoRetractFromSmallPropositionToProp.

(** * Inconsistency of the existence in the Calculus of Constructions with universes of a retract from some Type universe into Prop. *)

(** Note: Assuming the context [down:Type->Prop; up:Prop->Type; forth:
      forall (A:Type), A -> up (down A); back: forall (A:Type), up
      (down A) -> A; H: forall (A:Type) (P:A->Type) (a:A),
      P (back A (forth A a)) -> P a] is probably enough.  *)

Module NoRetractFromTypeToProp.

Definition Type2 := Type.
Definition Type1 := Type : Type2.

Section Paradox.

Notation "'rew1' <- H 'in' H'" := (@eq_rect_r Type1 _ (fun X : Type1 => X) H' _ H)
    (at level 10, H' at level 10).
Notation "'rew1' H 'in' H'" := (@eq_rect Type1 _ (fun X : Type1 => X) H' _ H)
    (at level 10, H' at level 10).

(** Assumption of a retract from Type into Prop *)

Variable down : Type1 -> Prop.
Variable up : Prop -> Type1.
Hypothesis up_down : forall (A:Type1), up (down A) = A :> Type1.

(** Proof *)

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
apply rew_opp_r with (P:=fun X:Type1 => X).
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

End NoRetractFromTypeToProp.

(** Application: Prop<>Type for some given Type *)

Import NoRetractFromTypeToProp.

Section Prop_neq_Type.

Notation "'rew2' <- H 'in' H'" := (@eq_rect_r Type2 _ (fun X : Type2 => X) H' _ H)
    (at level 10, H' at level 10).
Notation "'rew2' H 'in' H'" := (@eq_rect Type2 _ (fun X : Type2 => X) H' _ H)
    (at level 10, H' at level 10).

Variable Heq : Prop = Type1 :> Type2.

Definition down : Type1 -> Prop := fun A => rew2 <- Heq in A.
Definition up : Prop -> Type1 := fun A => rew2 Heq in A.

Lemma up_down : forall (A:Type1), up (down A) = A :> Type1.
Proof.
unfold up, down. rewrite Heq. reflexivity.
Defined.

Theorem Prop_neq_Type : False.
Proof.
apply paradox with down up.
apply up_down.
Qed.

End Prop_neq_Type.
