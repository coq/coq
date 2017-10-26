Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 6329 lines to 110 lines, then from 115 lines to 88 lines, then from 93 lines to 72 lines *)
(* coqc version trunk (September 2014) compiled on Sep 25 2014 2:53:46 with OCaml 4.01.0
   coqtop version cagnode16:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (bec7e0914f4a7144cd4efa8ffaccc9f72dbdb790) *)

Notation "( x ; y )" := (existT _ x y).
Notation "x .1" := (projT1 x) (at level 3, format "x '.1'").
Class IsEquiv {A B : Type} (f : A -> B) := { equiv_inv : B -> A }.
Record Equiv A B := { equiv_fun :> A -> B ; equiv_isequiv :> IsEquiv equiv_fun }.
Notation "A <~> B" := (Equiv A B) (at level 85).
Axiom IsHProp : Type -> Type.
Inductive Bool := true | false.
Definition negb (b : Bool) := if b then false else true.
Hypothesis LEM : forall A : Type, IsHProp A -> A + (A -> False).
Axiom cheat : forall {A},A.
Module NonPrim.
  Class Contr (A : Type) := { center : A ; contr : (forall y : A, center = y) }.
  Definition Book_6_9 : forall X, X -> X.
  Proof.
    intro X.
    pose proof (@LEM (Contr { f : X <~> X & ~(forall x, f x = x) }) cheat) as contrXEquiv.
    destruct contrXEquiv as [[f H]|H]; [ exact f.1 | exact (fun x => x) ].
  Defined.
  Lemma Book_6_9_not_id b : Book_6_9 Bool b = negb b.
  Proof.
    unfold Book_6_9.
    destruct (@LEM (Contr { f : Bool <~> Bool & ~(forall x, f x = x) }) _) as [[f H']|H'].
    match goal with
      | [ |- equiv_fun Bool Bool f.1 b  = negb b ] => idtac
      | [ |- equiv_fun Bool Bool center.1 b = negb b ] => fail 1 "bad"
    end.
    all:admit.
  Defined.
End NonPrim.
Module Prim.
  Set Primitive Projections.
  Class Contr (A : Type) := { center : A ; contr : (forall y : A, center = y) }.
  Definition Book_6_9 : forall X, X -> X.
  Proof.
    intro X.
    pose proof (@LEM (Contr { f : X <~> X & ~(forall x, f x = x) }) cheat) as contrXEquiv.
    destruct contrXEquiv as [[f H]|H]; [ exact (f.1) | exact (fun x => x) ].
  Defined.
  Lemma Book_6_9_not_id b : Book_6_9 Bool b = negb b.
  Proof.
    unfold Book_6_9.
    destruct (@LEM (Contr { f : Bool <~> Bool & ~(forall x, f x = x) }) _) as [[f H']|H']. 
    match goal with
      | [ |- equiv_fun Bool Bool f.1 b  = negb b ] => idtac
      | [ |- equiv_fun Bool Bool center.1 b = negb b ] => fail 1 "bad"
    end. (* Tactic failure: bad *)
    all:admit.
  Defined.
End Prim.
