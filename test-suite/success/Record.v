(* Nijmegen expects redefinition of sorts *)
Definition CProp := Prop.
Record test : CProp :=  {n : nat ; m : bool ; _ : n <> 0 }.
Require Import Program.
Require Import List.

Record vector {A : Type} {n : nat} := { vec_list : list A ; vec_len : length vec_list = n }.
Arguments vector : clear implicits.

Coercion vec_list : vector >-> list.

Hint Rewrite @vec_len : datatypes.

Ltac crush := repeat (program_simplify ; autorewrite with list datatypes ; auto with *).

Obligation Tactic := crush.

Program Definition vnil {A} : vector A 0 := {| vec_list := [] |}.

Program Definition vcons {A n} (a : A) (v : vector A n) : vector A (S n) :=
  {| vec_list := cons a (vec_list v) |}.

Hint Rewrite map_length rev_length : datatypes.

Program Definition vmap {A B n} (f : A -> B) (v : vector A n) : vector B n :=
  {| vec_list := map f v |}.

Program Definition vreverse {A n} (v : vector A n) : vector A n :=
  {| vec_list := rev v |}.

Fixpoint va_list {A B} (v : list (A -> B)) (w : list A) : list B :=
  match v, w with
    | nil, nil => nil
    | cons f fs, cons x xs => cons (f x) (va_list fs xs)
    | _, _ => nil
  end.

Program Definition va {A B n} (v : vector (A -> B) n) (w : vector A n) : vector B n :=
  {| vec_list := va_list v w |}.

Next Obligation.
  destruct v as [v Hv]; destruct w as [w Hw] ; simpl.
  subst n. revert w Hw. induction v ; destruct w ; crush.
  rewrite IHv ; auto.
Qed.

(* Correct type inference of record notation. Initial example by Spiwack. *)

Inductive Machin := {
 Bazar : option Machin
}.

Definition bli : Machin :=
 {| Bazar := Some ({| Bazar := None |}:Machin) |}.

Definition bli' : option (option Machin)  :=
 Some (Some {| Bazar := None |} ).

Definition bli'' : Machin :=
 {| Bazar := Some {| Bazar := None |} |}.

Definition bli''' := {| Bazar := Some {| Bazar := None |} |}.

(** Correctly use scoping information *)

Require Import ZArith.

Record Foo := { bar : Z }.
Definition foo := {| bar := 0 |}.

(** Notations inside records *)

Require Import Relation_Definitions.

Record DecidableOrder : Type :=
{ A : Type
; le : relation A where "x <= y" := (le x y)
; le_refl : reflexive _ le
; le_antisym : antisymmetric _ le
; le_trans : transitive _ le
; le_total : forall x y, {x <= y}+{y <= x}
}.

(* Test syntactic sugar suggested by wish report #2138 *)

Record R : Type := {
  P (A : Type) : Prop := exists x : A -> A, x = x;
  Q A : P A -> P A
}.

(* We allow reusing an implicit parameter named in non-recursive types *)
(* This is used in a couple of development such as UniMatch *)

Record S {A:Type} := { a : A; b : forall A:Type, A }.
