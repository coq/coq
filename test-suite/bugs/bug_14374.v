From Stdlib Require Import Arith.
Import Logic.EqNotations.

Definition le n m := forall p, p <= n -> p <= m.
Infix "<=" := le : nat_scope.

Definition le_refl n : n <= n :=
  fun _ x => (***** This "id" blocked unification *****) id x.

Definition le_trans {n m p} (Hnm : n <= m) (Hmp : m <= p) : n <= p :=
  fun q (Hqn : Peano.le q n) => Hmp _ (Hnm _ Hqn).
Infix "↕" := le_trans (at level 45).

Theorem le_S_up {n m} (Hnm : n <= m) : n <= S m.
  intros p Hpn.
  apply (Peano.le_S p m).
  apply Hnm.
  auto.
Defined.
Notation "↑ h" := (le_S_up h) (at level 40).

Theorem le_S_down {n m} (Hnm : S n <= m) : n <= m.
  unfold le.
  intros p Hpn.
  apply Hnm.
  apply Peano.le_S.
  auto.
Defined.
Notation "↓ p" := (le_S_down p) (at level 40).

Notation "x .+1" := (S x) (at level 1, left associativity, format "x .+1").
Notation "x .+2" := (S (S x)) (at level 1, left associativity, format "x .+2").

Set Printing Projections.

Record PartialBox {n p : nat} := {
  box (Hp : p <= n) : Type ;
  box' (Hp : p.+1 <= n) : Type ;
  box'' (Hp : p.+2 <= n) : Type ;
  subbox {q} {Hp : p.+1 <= q.+1} (Hq : q.+1 <= n) :
  box (↓ (Hp ↕ Hq)) -> box' (Hp ↕ Hq);
  subbox' {q} {Hp : p.+2 <= q.+2} (Hq : q.+2 <= n) :
  box' (↓ (Hp ↕ Hq)) -> box'' (Hp ↕ Hq);
  cohbox {q r} {Hpr : p.+2 <= r.+2} {Hr : r.+2 <= q.+1} {Hq : q.+1 <= n}
    (d : box (↓ ↓ (Hpr ↕ (Hr ↕ Hq)))) :
    subbox' (Hr ↕ Hq) (subbox (Hp:=↓le_refl _) (Hpr ↕ (Hr ↕ Hq)) d) =
      (subbox' (Hr ↕ Hq) (subbox (Hp:=↓le_refl _) (Hpr ↕ (Hr ↕ Hq)) d));
}.

Record PartialCube (n p : nat) (Box : forall {p}, PartialBox) := {
  cube {Hp : p <= n} :
    (Box.(box) (le_refl n) -> Type) -> Box.(box) Hp -> Type ;
  cube' {Hp : p.+1 <= n} :
    Box.(box') Hp -> Type ;
  cube'' {Hp : p.+2 <= n} :
    Box.(box'') Hp -> Type ;
  subcube {q} {Hp : p.+1 <= q.+1}
    (Hq : q.+1 <= n)
    {E : Box.(box) (le_refl n) -> Type}
    {d : Box.(box) (↓ (Hp ↕ Hq))} (b : cube E d) :
    cube' (Box.(subbox) Hq d) ;
  subcube' {q} {Hp : p.+2 <= q.+2}
    (Hq : q.+2 <= n)
    {d : Box.(box') (↓ (Hp ↕ Hq))} (b : cube' d) :
    cube'' (Box.(subbox') Hq d) ;
  cohcube {q r} {Hp : p.+2 <= r.+2}
    {Hr : r.+2 <= q.+1} {Hq : q.+1 <= n}
    (E : Box.(box) (le_refl n) -> Type)
    (d : Box.(box) (↓ ↓ (Hp ↕ (Hr ↕ Hq)))) (b : cube E d) :
    (***** This used to fail if "id" was present in the proof of le_refl *****)
    rew (Box.(cohbox) d) in
    (subcube' _ (subcube _ b)) = (subcube' _ (subcube _ b))
}.
