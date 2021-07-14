Axiom P : Prop.
Definition Q := True -> P.

(* bug 13778, 5394 *)
Goal Q -> Q.
Proof.
  intro.
  Fail congruence.
  simple congruence.
Qed.

Goal (not P) -> P -> False.
Proof. simple congruence. Qed.

Goal (P -> False) -> not P.
Proof.
  simple congruence.
Qed.

Fixpoint slow (n: nat): bool :=
  match n with
  | O => true
  | S m => andb (slow m) (slow (pred m))
  end.

Parameter f: nat -> nat.

Definition foo(n b: nat): Prop :=
  if slow n then (forall a, f a = f b) else True.

(* fail fast symbolically *)
(* bug 13189 *)
Goal forall a b, foo 27 b -> f a = f b.
Proof.
  Timeout 1 Fail Time simple congruence.
  (* Fail Timeout 1 Time congruence. *)
Admitted.

(* succeed fast symbolically *)
(* bug 13189 *)
Goal forall a b, foo 29 b -> f b = f a -> f a = f b.
Proof.
  (* Fail Timeout 1 Time congruence. *)
  Timeout 1 simple congruence.
Qed.

Goal True -> not True -> P.
Proof. simple congruence. Qed.

(* consider final not *)
Goal False -> not True.
Proof. simple congruence. Qed.

(* consider final not *)
Goal not (true = false).
Proof. simple congruence. Qed.

Fixpoint stupid (n : nat) : unit :=
match n with
| 0 => tt
| S n =>
  let () := stupid n in
  let () := stupid n in
  tt
end.

(* do not try to unify 23 with stupid 23 *)
Goal 23 = 23 -> stupid 23 = stupid 23.
Proof. Timeout 1 simple congruence. Qed.

Inductive Fin : nat -> Set :=
| F1 : forall n : nat, Fin (S n)
| FS : forall n : nat, Fin n -> Fin (S n).

(* indexed inductives *)
Goal forall n (f : Fin n), FS n f = F1 n -> False.
Proof. intros n f H. simple congruence. Qed.

Axiom R : Prop.
Axiom R' : Prop.

Goal (not P) -> not P.
Proof. simple congruence. Qed.

Goal (P -> False) -> P -> False.
Proof. simple congruence. Qed.

Goal (not (true = true)) -> P.
Proof. simple congruence. Qed.

Goal Q -> (Q = R) -> R.
Proof. simple congruence. Qed.

(* unfortunately, common usecase *)
Goal P -> Q.
Proof.
  Fail simple congruence.
  repeat intro. simple congruence.
Qed.

(* bug 13778 *)
Goal R -> (R = not P) -> not P.
Proof.
  Fail congruence.
  simple congruence.
Qed.

Definition per_unit := forall u, match u with tt => True end.

(* bug 5394 *)
Goal per_unit -> per_unit.
Proof. simple congruence. Qed.
