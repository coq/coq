Set Universe Polymorphism.

Inductive bool@{q| |} : Type@{q|Set} := | true : bool | false : bool.

Definition nand@{q| |} (a b : bool@{q|}) : bool@{q|} :=
  match a , b with
  | true , true => false
  | _ , _ => true
  end.

Inductive seq@{q|u|} {A : Type@{q|u}} (a : A) : A -> Type@{q|u} := | srefl : seq a a.
Arguments srefl {_ _}.

Definition seq_elim@{q|u v|} :=
  fun (A : Type@{q|u}) (x : A) (P : A -> Type@{q|v}) (f : P x) (a : A) (e : seq x a) =>
  match e in (seq _ a0) return (P a0) with
  | srefl => f
  end.

Register seq as core.eq.type.
Register srefl as core.eq.refl.
Register seq_elim as core.eq.rect.

Lemma foo@{q| |} (f : bool@{q|} -> bool@{q|}) (x : bool@{q|}) : seq (f true) (f true).
Proof.
  remember (f true) as b eqn : ftrue.
  reflexivity.
Qed.

Lemma f3_eq_f@{q| |} (f : bool@{q|} -> bool@{q|}) (x : bool@{q|}) : seq (f (f (f x))) (f x).
Proof.
  remember (f true) as b eqn : ftrue.

  remember (f false) as c eqn : ffalse.
  Validate Proof.

  destruct x,b,c.
  all:repeat rewrite <-?ftrue, <-?ffalse.
  all: reflexivity.
Qed.
