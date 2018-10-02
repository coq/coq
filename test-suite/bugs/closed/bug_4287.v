Unset Strict Universe Declaration.

Universe b.

Universe c.

Definition U : Type@{b} := Type@{c}.

Module Type MT.

Definition T := Prop.
End MT.

Module M : MT.
   Definition T := Type@{b}.

Print Universes.
Fail End M.

Set Universe Polymorphism.

(* This is a modified version of Hurkens with all universes floating *)
Section Hurkens.

Variable down : Type -> Type.
Variable up : Type -> Type.

Hypothesis back : forall A, up (down A) -> A.

Hypothesis forth : forall A, A -> up (down A).

Hypothesis backforth : forall (A:Type) (P:A->Type) (a:A),
      P (back A (forth A a)) -> P a.

Hypothesis backforth_r : forall (A:Type) (P:A->Type) (a:A),
      P a -> P (back A (forth A a)).

(** Proof *)
Definition V : Type := forall A:Type, ((up A -> Type) -> up A -> Type) -> up A -> Type.
Definition U : Type := V -> Type.

Definition sb (z:V) : V := fun A r a => r (z A r) a.
Definition le (i:U -> Type) (x:U) : Type := x (fun A r a => i (fun v => sb v A r a)).
Definition le' (i:up (down U) -> Type) (x:up (down U)) : Type := le (fun a:U => i (forth _ a)) (back _ x).
Definition induct (i:U -> Type) : Type := forall x:U, up (le i x) -> up (i x).
Definition WF : U := fun z => down (induct (fun a => z (down U) le' (forth _ a))).
Definition I (x:U) : Type :=
  (forall i:U -> Type, up (le i x) -> up (i (fun v => sb v (down U) le' (forth _ x)))) -> False.

Lemma Omega : forall i:U -> Type, induct i -> up (i WF).
Proof.
intros i y.
apply y.
unfold le, WF, induct.
apply forth.
intros x H0.
apply y.
unfold sb, le', le.
compute.
apply backforth_r.
exact H0.
Qed.

Lemma lemma1 : induct (fun u => down (I u)).
Proof.
unfold induct.
intros x p.
apply forth.
intro q.
generalize (q (fun u => down (I u)) p).
intro r.
apply back in r.
apply r.
intros i j.
unfold le, sb, le', le in j |-.
apply backforth in j.
specialize q with (i := fun y => i (fun v:V => sb v (down U) le' (forth _ y))).
apply q.
exact j.
Qed.

Lemma lemma2 : (forall i:U -> Type, induct i -> up (i WF)) -> False.
Proof.
intro x.
generalize (x (fun u => down (I u)) lemma1).
intro r; apply back in r.
apply r.
intros i H0.
apply (x (fun y => i (fun v => sb v (down U) le' (forth _ y)))).
unfold le, WF in H0.
apply back in H0.
exact H0.
Qed.

Theorem paradox : False.
Proof.
exact (lemma2 Omega).
Qed.

End Hurkens.

Polymorphic Record box (T : Type) := wrap {unwrap : T}.

(* Here we instantiate to Set *)

Fail Definition down (x : Type) : Prop := box x.
Definition up (x : Prop) : Type := x.

Fail Definition back A : up (down A) -> A := unwrap A.

Fail Definition forth A : A -> up (down A) := wrap A.

Definition id {A : Type} (a : A) := a.
Definition setlt (A : Type@{i}) :=
  let foo := Type@{i} : Type@{j} in True.

Definition setle (B : Type@{i}) :=
  let foo (A : Type@{j}) := A in foo B.

Fail Check @setlt@{j Prop}.
Fail Definition foo := @setle@{j Prop}.
Check setlt@{Set i}.
Check setlt@{Set j}.
