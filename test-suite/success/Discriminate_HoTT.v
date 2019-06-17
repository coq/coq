(* -*- mode: coq; coq-prog-args: ("-noinit" "-indices-matter") -*- *)

(* This file tests the discriminate tactic compatibility with HoTT.
   The first part of the file will setup a mini HoTT environment.
   Afterwards a number of tests are performed. The tests are basically
   copied from the Discriminate.v test file. *)

Unset Elimination Schemes.

Set Universe Polymorphism.

Declare ML Module "ltac_plugin".

Global Set Default Proof Mode "Classic".

Notation "x -> y" := (forall (_:x), y) (at level 99, right associativity, y at level 200).

Cumulative Variant paths {A} (a:A) : A -> Type
  := idpath : paths a a.

Arguments idpath {A a} , [A] a.

Scheme paths_ind := Induction for paths Sort Type.
Arguments paths_ind [A] a P f y p.

Notation "x = y :> A" := (@paths A x y) (at level 70, y at next level, no associativity).
Notation "x = y" := (x = y :>_) (at level 70, no associativity).

Register paths as core.identity.type.
Register idpath as core.identity.refl.
Register paths_ind as core.identity.ind.

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.
Arguments inverse {A x y} p : simpl nomatch.
Register inverse as core.identity.sym.

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.
Arguments concat {A x y z} p q : simpl nomatch.
Register concat as core.identity.trans.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.
Arguments ap {A B} f {x y} p.
Register ap as core.identity.congr.

Variant Empty : Type :=.

Register Empty as core.False.type.

Variant Unit : Type := tt.

Register Unit as core.True.type.
Register tt as core.True.I.

Variant Bool : Type := true | false.

Inductive nat : Type := O | S (n:nat).

(*********** Test discriminate tactic below. ***************)

Goal O = S O -> Empty.
 discriminate 1.
Qed.

Goal forall H : O = S O, H = H.
 discriminate H.
Qed.

Goal O = S O -> Unit.
intros. discriminate H. Qed.
Goal O = S O -> Unit.
intros. Ltac g x := discriminate x. g H. Qed.

Goal (forall x y : nat, x = y -> x = S y) -> Unit.
intros.
try discriminate (H O) || exact tt.
Qed.

Goal (forall x y : nat, x = y -> x = S y) -> Unit.
intros. ediscriminate (H O). instantiate (1:=O). Abort.

(* Check discriminate on types with local definitions *)

Inductive A := B (T := Unit) (x y : Bool) (z := x).
Goal forall x y, B x true = B y false -> Empty.
discriminate.
Qed.
