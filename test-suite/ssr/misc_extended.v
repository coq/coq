Require Import ssreflect.

(* Require Import List. *)

Lemma test_elim_pattern_1 : forall A (l:list A), app l nil = l.
Proof.
intros A.
elim/list_ind => [^~ 1 ].
  by [].
match goal with |- app (cons a1 l1) nil = cons a1 l1 => idtac end.
Abort.

Lemma test_elim_pattern_2 : forall A (l:list A), app l nil = l.
Proof.
intros. elim: l => [^~ 1 ].
  by [].
match goal with |- app (cons a1 l1) nil = cons a1 l1 => idtac end.
Abort.

Lemma test_elim_pattern_3 : forall A (l:list A), app l nil = l.
Proof.
intros. elim: l => [ | x l' IH ].
  by [].
match goal with |- app (cons x l') nil = cons x l' => idtac end.
Abort.


Generalizable Variables A.

Class Inhab (A:Type) : Type :=
  { arbitrary : A }.

Lemma test_intro_typeclass_1 : forall A `{Inhab A} (l1 l2:list A), l2 = nil -> app l1 l2 = l1.
Proof.
move =>> H.
  match goal with |- _ = _ => idtac end.
Abort.

Lemma test_intro_typeclass_2 : forall A `{Inhab A} (x:A), x = arbitrary -> x = arbitrary.
Proof.
move =>> H.
  match goal with |- _ = _ => idtac end.
Abort.

Lemma test_intro_temporary_1 : forall A (l1 l2:list A), l2 = nil -> app l1 l2 = l1.
Proof.
move => A + l2.
  match goal with |- forall l1, l2 = nil -> app l1 l2 = l1 => idtac end.
Abort.

Lemma test_intro_temporary_2 : forall A `{Inhab A} (l1 l2:list A), l2 = nil -> app l1 l2 = l1.
Proof.
move => > E.
  match goal with |- _ = _ => idtac end.
Abort.

Lemma test_dispatch : (forall x:nat, x= x )/\ (forall y:nat, y = y).
Proof.
intros. split => [ a | b ].
  match goal with |- a = a => by [] end.
match goal with |- b = b => by [] end.
Abort.

Lemma test_tactics_as_view_1 : forall A (l1:list A), app nil l1 = l1.
Proof.
move => /ltac:(simpl).
Abort.

Lemma test_tactics_as_view_2 : forall A, (forall (l1:list A), app nil l1 = l1) /\ (app nil nil = @nil A).
Proof.
move => A.
(* TODO: I want to do  [split =>.] as a temporary step in setting up my script,
    but this syntax does not seem to be supported. Can't we have an empty ipat?
   Note that I can do [split => [ | ]]*)
split => [| /ltac:(simpl)].
Abort.

Notation "%%" := (ltac:(simpl)) (only parsing) : ssripat_scope.

Lemma test_tactics_as_view_3 : forall A, (forall (l1:list A), app nil l1 = l1) /\ (app nil nil = @nil A).
Proof.
move => /ltac:(split) [ | /%% ].
Abort.
