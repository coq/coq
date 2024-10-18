(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Set Implicit Arguments.
(* Set Universe Polymorphism. *)

(******************************************************************)
(** * Basics: definition of polymorphic lists and some operations *)
(******************************************************************)

#[local] Open Scope bool_scope.
Open Scope list_scope.

(************)
(** ** Map  *)
(************)

Section Map.

  Variables (A : Type) (B : Type).
  Variable f : A -> B.

  Fixpoint map (l:list A) : list B :=
    match l with
      | nil => nil
      | a :: t => (f a) :: (map t)
    end.

End Map.

Section NatSeq.

  (** [seq] computes the sequence of [len] contiguous integers
      that starts at [start]. For instance, [seq 2 3] is [2::3::4::nil]. *)

  Fixpoint seq (start len:nat) : list nat :=
    match len with
      | 0 => nil
      | S len => start :: seq (S start) len
    end.

End NatSeq.

Section Repeat.

  Variable A : Type.
  Fixpoint repeat (x : A) (n: nat ) :=
    match n with
      | O => nil
      | S k => x :: repeat x k
    end.

End Repeat.

Section Elts.

  Variable A : Type.

  (*****************************)
  (** ** Nth element of a list *)
  (*****************************)

  Fixpoint nth (n:nat) (l:list A) (default:A) {struct l} : A :=
    match n, l with
      | O, x :: l' => x
      | O, nil => default
      | S m, nil => default
      | S m, x :: t => nth m t default
    end.

End Elts.

Section Cutting.

  Variable A : Type.

  Fixpoint firstn (n:nat)(l:list A) : list A :=
    match n with
      | 0 => nil
      | S n => match l with
                 | nil => nil
                 | a::l => a::(firstn n l)
               end
    end.

  Fixpoint skipn (n:nat)(l:list A) : list A :=
    match n with
      | 0 => l
      | S n => match l with
                 | nil => nil
                 | a::l => skipn n l
               end
    end.

End Cutting.

Section Exists_Forall.

  (** * Existential and universal predicates over lists *)

  Variable A:Type.

  Section One_predicate.

    Variable P : A -> Prop.

    Inductive Forall : list A -> Prop :=
      | Forall_nil : Forall nil
      | Forall_cons : forall x l, P x -> Forall l -> Forall (x :: l).

  End One_predicate.

End Exists_Forall.

(***********************)
(** ** List comparison *)
(***********************)

Section Compare.

  Variable A : Type.
  Variable cmp : A -> A -> comparison.

  Fixpoint list_compare (xs ys : list A) : comparison :=
    match xs, ys with
    | nil   , nil    => Eq
    | nil   , _      => Lt
    | _     , nil    => Gt
    | x :: xs, y :: ys =>
        match cmp x y with
        | Eq => list_compare xs ys
        | c  => c
        end
    end%list.

End Compare.

Unset Universe Polymorphism.
