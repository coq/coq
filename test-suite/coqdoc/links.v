(** Various checks for coqdoc

- symbols should not be inlined in string g
- links to both kinds of notations in a' should work to the right notation
- with utf8 option, forall must be unicode
- splitting between symbols and ident should be correct in a' and c
- ".." should be rendered correctly
*)

Require Import String.

Definition g := "dfjkh""sdfhj forall <> * ~"%string.

Definition a (b: nat) := b.

Definition f := forall C:Prop, C.

Notation "n ++ m" := (plus n m).

Notation "n ++ m" := (mult n m). (* redefinition *)

Notation "n ** m" := (plus n m) (at level 60).

Notation "n ▵ m" := (plus n m) (at level 60).

Notation "n '_' ++ 'x' m" := (plus n m) (at level 3).

Inductive eq (A:Type) (x:A) : A -> Prop := eq_refl : x = x :>A

where "x = y :> A" := (@eq A x y) : type_scope.

Definition eq0 := 0 = 0 :> nat.

Notation "( x # y ; .. ; z )" := (pair .. (pair x y) .. z).

Definition b_α := ((0#0;0) , (0 ** 0)).

Notation h := a.

  Section test.

    Variables b' b2: nat.

    Notation "n + m" := (n ▵ m) : my_scope.

    Delimit Scope my_scope with my.

    Notation l := 0.

    Definition α := (0 + l)%my.

    Definition a' b := b'++0++b2 _ ++x b.

    Definition c := {True}+{True}.

    Definition d := (1+2)%nat.

    Lemma e : nat + nat.
    Admitted.

  End test.

  Section test2.

    Variables b': nat.

    Section test.

      Variables b2: nat.

      Definition a'' b := b' ++ O ++ b2 _ ++ x b + h 0.

    End test.

  End test2.

(** skip *)

(** skip *)

(** skip *)

(** skip *)

(** skip *)

(** skip *)

(** skip *)

(** skip *)

(** skip *)

(** skip *)

(** skip *)

(** skip *)

(** skip *)

(** skip *)

