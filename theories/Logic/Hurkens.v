(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                              Hurkens.v                               *)
(************************************************************************)

(** This is Hurkens paradox [Hurkens] in system U-, adapted by Herman
    Geuvers [Geuvers] to show the inconsistency in the pure calculus of
    constructions of a retract from Prop into a small type.

    References:

    - [Hurkens] A. J. Hurkens, "A simplification of Girard's paradox",
      Proceedings of the 2nd international conference Typed Lambda-Calculi
      and Applications (TLCA'95), 1995.

    - [Geuvers] "Inconsistency of Classical Logic in Type Theory", 2001
      (see www.cs.kun.nl/~herman/note.ps.gz).
*)

Section Paradox.

Variable bool : Prop.
Variable p2b : Prop -> bool.
Variable b2p : bool -> Prop.
Hypothesis p2p1 : forall A:Prop, b2p (p2b A) -> A.
Hypothesis p2p2 : forall A:Prop, A -> b2p (p2b A).
Variable B : Prop.

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
unfold le, WF, induct in |- *.
apply p2p2.
intros x H0.
apply y.
exact H0.
Qed.

Lemma lemma1 : induct (fun u => p2b (I u)).
Proof.
unfold induct in |- *.
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
