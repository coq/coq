(* Check that the encoding of system U- fails *)

Inductive prop : Prop := down : Prop -> prop.

Definition up (p:prop) : Prop := let (A) := p in A.

Lemma p2p1 : forall A:Prop, up (down A) -> A.
Proof.
exact (fun A x => x).
Qed.

Lemma p2p2 : forall A:Prop, A -> up (down A).
Proof.
exact (fun A x => x).
Qed.

(** Hurkens' paradox *)

Definition V := forall A:Prop, ((A -> prop) -> A -> prop) -> A -> prop.
Definition U := V -> prop.
Definition sb (z:V) : V := fun A r a => r (z A r) a.
Definition le (i:U -> prop) (x:U) : prop :=
  x (fun A r a => i (fun v => sb v A r a)).
Definition induct (i:U -> prop) : Prop :=
  forall x:U, up (le i x) -> up (i x).
Definition WF : U := fun z => down (induct (z U le)).
Definition I (x:U) : Prop :=
  (forall i:U -> prop, up (le i x) -> up (i (fun v => sb v U le x))) -> False.

Lemma Omega : forall i:U -> prop, induct i -> up (i WF).
Proof.
intros i y.
apply y.
unfold le, WF, induct in |- *.
intros x H0.
apply y.
exact H0.
Qed.

Lemma lemma1 : induct (fun u => down (I u)).
Proof.
unfold induct in |- *.
intros x p.
intro q.
apply (q (fun u => down (I u)) p).
intro i.
apply q with (i := fun y => i (fun v:V => sb v U le y)).
Qed.

Lemma lemma2 : (forall i:U -> prop, induct i -> up (i WF)) -> False.
Proof.
intro x.
apply (x (fun u => down (I u)) lemma1).
intros i H0.
apply (x (fun y => i (fun v => sb v U le y))).
apply H0.
Qed.

Theorem paradox : False.
Proof.
exact (lemma2 Omega).
Qed.
