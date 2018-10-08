Require Import TestSuite.admit.
Set Universe Polymorphism.
Definition Lift
: ltac:(let U1 := constr:(Type) in
    let U0 := constr:(Type : U1) in
    exact (U0 -> U1))
  := fun T => T.

Fail Check nat:Prop. (* The command has indeed failed with message:
=> Error:
The term "nat" has type "Set" while it is expected to have type "Prop". *)
Set Printing All.
Set Printing Universes.
Fail Check Lift nat : Prop. (* Lift (* Top.8 Top.9 Top.10 *) nat:Prop
     : Prop
(* Top.10
   Top.9
   Top.8 |= Top.10 < Top.9
             Top.9 < Top.8
             Top.9 <= Prop
              *)
 *)
Fail Eval compute in Lift nat : Prop.
(*      = nat
     : Prop *)

Section Hurkens.

  Monomorphic Definition Type2 := Type.
  Monomorphic Definition Type1 := Type : Type2.

  (** Assumption of a retract from Type into Prop *)

  Variable down : Type1 -> Prop.
  Variable up : Prop -> Type1.

  Hypothesis back : forall A, up (down A) -> A.

  Hypothesis forth : forall A, A -> up (down A).

  Hypothesis backforth : forall (A:Type) (P:A->Type) (a:A),
                           P (back A (forth A a)) -> P a.

  Hypothesis backforth_r : forall (A:Type) (P:A->Type) (a:A),
                             P a -> P (back A (forth A a)).

  (** Proof *)

  Definition V : Type1 := forall A:Prop, ((up A -> Prop) -> up A -> Prop) -> up A -> Prop.
  Definition U : Type1 := V -> Prop.

  Definition sb (z:V) : V := fun A r a => r (z A r) a.
  Definition le (i:U -> Prop) (x:U) : Prop := x (fun A r a => i (fun v => sb v A r a)).
  Definition le' (i:up (down U) -> Prop) (x:up (down U)) : Prop := le (fun a:U => i (forth _ a)) (back _ x).
  Definition induct (i:U -> Prop) : Type1 := forall x:U, up (le i x) -> up (i x).
  Definition WF : U := fun z => down (induct (fun a => z (down U) le' (forth _ a))).
  Definition I (x:U) : Prop :=
    (forall i:U -> Prop, up (le i x) -> up (i (fun v => sb v (down U) le' (forth _ x)))) -> False.

  Lemma Omega : forall i:U -> Prop, induct i -> up (i WF).
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

  Lemma lemma2 : (forall i:U -> Prop, induct i -> up (i WF)) -> False.
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

Definition informative (x : bool) :=
  match x with
    | true => Type
    | false => Prop
  end.

Definition depsort (T : Type) (x : bool) : informative x :=
  match x with
    | true => T
    | false => True
  end.

(** This definition should fail *)
Fail Definition Box (T : Type1) : Prop := Lift T.

Fail Definition prop {T : Type1} (t : Box T) : T := t.
Fail Definition wrap {T : Type1} (t : T) : Box T := t.

Fail Definition down (x : Type1) : Prop := Box x.
Definition up (x : Prop) : Type1 := x.

Fail Definition back A : up (down A) -> A := @prop A.

Fail Definition forth (A : Type1) : A -> up (down A) := @wrap A.

Fail Definition backforth (A:Type1) (P:A->Type) (a:A) :
      P (back A (forth A a)) -> P a := fun H => H.

Fail Definition backforth_r (A:Type1) (P:A->Type) (a:A) :
      P a -> P (back A (forth A a)) := fun H => H.

Theorem pandora : False.
  Fail apply (paradox down up back forth backforth backforth_r).
  admit.
Qed.

Print Assumptions pandora.
