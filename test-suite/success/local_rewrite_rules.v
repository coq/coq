(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Module Type Plus.
  Symbol plus : nat -> nat -> nat.
  Rewrite Rules plus_r :=
  | plus 0 ?n => ?n
  | plus (S ?m) ?n => S (plus ?m ?n).
End Plus.

Module Import PlusImpl : Plus. Definition plus := Nat.add. End PlusImpl.

Check eq_refl : plus 25 17 = 42.





Module Type QuotientInput.

Parameter A : Type.
Parameter eq : A -> A -> Prop.

End QuotientInput.


Module Type Quotient (Import QI : QuotientInput).

Parameter T : Type.

Symbol mk : A -> T.
Symbol lift : forall {B : Type} (f : A -> B) (p : forall a b, eq a b -> f a = f b), T -> B.

Rewrite Rule lift_mk :=
| lift ?f _ (mk ?x) => ?f ?x.

Parameter rec : forall {B : T -> SProp} (f : forall (a : A), B (mk a)) (t : T), B t.
Parameter sound : forall a b, eq a b -> mk a = mk b.

End Quotient.

Module QuotientImpl (Import QI : QuotientInput) : Quotient QI.

Definition T := A.

Definition mk (x : A) := x.
Definition lift {B} (f : A -> B) (p : forall a b, eq a b -> f a = f b) x := f x.

Definition rec {B : T -> SProp} (f : forall (a : A), B a) t := f t.

Axiom sound : forall a b, eq a b -> mk a = mk b.

End QuotientImpl.




Module Type Nat.

Parameter nat : Type.
Symbol O : nat.
Symbol S : nat -> nat.

Symbol nat_rect : forall P : nat -> Type, P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n.

Rewrite Rules nat_elim :=
| nat_rect _ ?z ?s O => ?z
| nat_rect ?P ?z ?s (S ?n) => ?s ?n (nat_rect ?P ?z ?s ?n).

End Nat.

Inductive Vec {A : Type} : nat -> Type :=
| vnil : Vec 0
| vcons {n} : A -> Vec n -> Vec (S n).
Arguments Vec : clear implicits.

Inductive All {A : Type} {P : A -> Type} : forall {n}, Vec A n -> Type :=
| Allvnil : All vnil
| Allvcons a (H : P a) {n} (v : Vec A n) : All v -> All (vcons a v).
Arguments All {_} P {n} _.

Unset Elimination Schemes.
Inductive W A (rec : A -> nat) := C (a : A) (r : Vec (W A rec) (rec a)).
Set Elimination Schemes.

Definition W_rect A rec (P : W A rec -> Type)
  (X : forall a v, All P v -> P (C _ _ a v)) :
  forall w, P w.
Proof.
  fix frec 1. destruct w.
  apply X.
  revert r. generalize (rec a) as n.
  induction r.
  - constructor.
  - constructor; auto.
Defined.


Module Import NatW : Nat.

Definition nat := W bool (fun b => if b then 1 else 0).

Definition O : nat := C _ _ false vnil.
Definition S (n : nat) : nat := C _ _ true (vcons n vnil).

Definition nat_rect (P : nat -> Type) (z : P O) (s : forall n, P n -> P (S n)) : forall n, P n.
Proof.
  induction n using W_rect. destruct a.
  - refine (match X with Allvcons a H v X => _ end). destruct n. 2: now intro. refine (match X with Allvnil => _ end).
    apply s. apply H.
  - refine (match X with Allvnil => _ end). apply z.
Defined.

End NatW.

Definition of_uint n := match n with Number.UIntDecimal n => Some (Datatypes.nat_rect _ O (fun _ => S) (Nat.of_uint n)) | _ => None end.
Definition to_uint (n : nat) : option Number.uint := None.

Number Notation NatW.nat Nat.of_num_int Nat.to_num_int (via Datatypes.nat mapping [O => Datatypes.O, S => Datatypes.S]): nat_scope.

Definition plus (m n : nat) := nat_rect _ n (fun _ => S) m.

Notation "m + n" := (plus m n).


Lemma plus_assoc (m n p : nat) : m + n + p = m + (n + p).
Proof.
  induction m using nat_rect.
  - cbn. reflexivity.
  - cbn. lazy in IHm. rewrite IHm. reflexivity.
Qed.

Check eq_refl : 25 + 9 + 8 = 42.
