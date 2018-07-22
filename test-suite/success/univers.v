(* This requires cumulativity *)

Definition Type2 := Type.
Definition Type1 : Type2 := Type.

Lemma lem1 : (True -> Type1) -> Type2.
intro H.
apply H.
exact I.
Qed.

Lemma lem2 :
 forall (A : Type) (P : A -> Type) (x : A),
 (forall y : A, x = y -> P y) -> P x.
auto.
Qed.

Lemma lem3 : forall P : Prop, P.
intro P; pattern P.
apply lem2.
Abort.

(* Check managing of universe constraints in inversion (BZ#855) *)

Inductive dep_eq : forall X : Type, X -> X -> Prop :=
  | intro_eq : forall (X : Type) (f : X), dep_eq X f f
  | intro_feq :
      forall (A : Type) (B : A -> Type),
      let T := forall x : A, B x in
      forall (f g : T) (x : A), dep_eq (B x) (f x) (g x) -> dep_eq T f g.

Require Import Relations.

Theorem dep_eq_trans : forall X : Type, transitive X (dep_eq X).
Proof.
  unfold transitive.
  intros X f g h H1 H2.
  inversion H1.
Abort.


(* Submitted by Bas Spitters (BZ#935) *)

(* This is a problem with the status of the type in LetIn: is it a
   user-provided one or an inferred one? At the current time, the
   kernel type-check the type in LetIn, which means that it must be
   considered as user-provided when calling the kernel. However, in
   practice it is inferred so that a universe refresh is needed to set
   its status as "user-provided".

   Especially, universe refreshing was not done for "set/pose" *)

Lemma ind_unsec : forall Q : nat -> Type, True.
intro.
set (C := forall m, Q m -> Q m).
exact I.
Qed.

(* Submitted by Danko Ilik (bug report #1507); related to LetIn *)

Record U : Type := { A:=Type; a:A }.

(** Check assignment of sorts to inductives and records. *)

Variable sh : list nat.

Definition is_box_in_shape (b :nat * nat) := True.
Definition myType := Type.

Module Ind.
Inductive box_in : myType :=
  myBox (coord : nat * nat) (_ : is_box_in_shape coord) : box_in.
End Ind.

Module Rec.
Record box_in : myType :=
  BoxIn { coord :> nat * nat; _ : is_box_in_shape coord }.
End Rec.
