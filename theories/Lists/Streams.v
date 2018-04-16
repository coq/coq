(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Set Implicit Arguments.

(** Streams *)

Section Streams.

Variable A : Type.

CoInductive Stream : Type :=
    Cons : A -> Stream -> Stream.


Definition hd (x:Stream) := match x with
                            | Cons a _ => a
                            end.

Definition tl (x:Stream) := match x with
                            | Cons _ s => s
                            end.


Fixpoint Str_nth_tl (n:nat) (s:Stream) : Stream :=
  match n with
  | O => s
  | S m => Str_nth_tl m (tl s)
  end.

Definition Str_nth (n:nat) (s:Stream) : A := hd (Str_nth_tl n s).


Lemma unfold_Stream :
 forall x:Stream, x = match x with
                      | Cons a s => Cons a s
                      end.
Proof.
  intro x.
  case x.
  trivial.
Qed.

Lemma tl_nth_tl :
 forall (n:nat) (s:Stream), tl (Str_nth_tl n s) = Str_nth_tl n (tl s).
Proof.
  simple induction n; simpl; auto.
Qed.
Hint Resolve tl_nth_tl: datatypes.

Lemma Str_nth_tl_plus :
 forall (n m:nat) (s:Stream),
   Str_nth_tl n (Str_nth_tl m s) = Str_nth_tl (n + m) s.
simple induction n; simpl; intros; auto with datatypes.
rewrite <- H.
rewrite tl_nth_tl; trivial with datatypes.
Qed.

Lemma Str_nth_plus :
 forall (n m:nat) (s:Stream), Str_nth n (Str_nth_tl m s) = Str_nth (n + m) s.
intros; unfold Str_nth; rewrite Str_nth_tl_plus;
 trivial with datatypes.
Qed.

(** Extensional Equality between two streams  *)

CoInductive EqSt (s1 s2: Stream) : Prop :=
    eqst :
        hd s1 = hd s2 -> EqSt (tl s1) (tl s2) -> EqSt s1 s2.

(** A coinduction principle *)

Ltac coinduction proof :=
  cofix proof; intros; constructor;
   [ clear proof | try (apply proof; clear proof) ].


(** Extensional equality is an equivalence relation *)

Theorem EqSt_reflex : forall s:Stream, EqSt s s.
coinduction EqSt_reflex.
reflexivity.
Qed.

Theorem sym_EqSt : forall s1 s2:Stream, EqSt s1 s2 -> EqSt s2 s1.
coinduction Eq_sym.
case H; intros; symmetry ; assumption.
case H; intros; assumption.
Qed.


Theorem trans_EqSt :
 forall s1 s2 s3:Stream, EqSt s1 s2 -> EqSt s2 s3 -> EqSt s1 s3.
coinduction Eq_trans.
transitivity (hd s2).
case H; intros; assumption.
case H0; intros; assumption.
apply (Eq_trans (tl s1) (tl s2) (tl s3)).
case H; trivial with datatypes.
case H0; trivial with datatypes.
Qed.

(** The definition given is equivalent to require the elements at each
    position to be equal *)

Theorem eqst_ntheq :
 forall (n:nat) (s1 s2:Stream), EqSt s1 s2 -> Str_nth n s1 = Str_nth n s2.
unfold Str_nth; simple induction n.
intros s1 s2 H; case H; trivial with datatypes.
intros m hypind.
simpl.
intros s1 s2 H.
apply hypind.
case H; trivial with datatypes.
Qed.

Theorem ntheq_eqst :
 forall s1 s2:Stream,
   (forall n:nat, Str_nth n s1 = Str_nth n s2) -> EqSt s1 s2.
coinduction Equiv2.
apply (H 0).
intros n; apply (H (S n)).
Qed.

Section Stream_Properties.

Variable P : Stream -> Prop.

(*i
Inductive Exists : Stream -> Prop :=
  | Here    : forall x:Stream, P x -> Exists x
  | Further : forall x:Stream, ~ P x -> Exists (tl x) -> Exists x.
i*)

Inductive Exists ( x: Stream ) : Prop :=
  | Here : P x -> Exists x
  | Further : Exists (tl x) -> Exists x.

CoInductive ForAll (x: Stream) : Prop :=
    HereAndFurther : P x -> ForAll (tl x) -> ForAll x.

Lemma ForAll_Str_nth_tl : forall m x, ForAll x -> ForAll (Str_nth_tl m x).
Proof.
induction m.
 tauto.
intros x [_ H].
simpl.
apply IHm.
assumption.
Qed.

Section Co_Induction_ForAll.
Variable Inv : Stream -> Prop.
Hypothesis InvThenP : forall x:Stream, Inv x -> P x.
Hypothesis InvIsStable : forall x:Stream, Inv x -> Inv (tl x).

Theorem ForAll_coind : forall x:Stream, Inv x -> ForAll x.
coinduction ForAll_coind; auto.
Qed.
End Co_Induction_ForAll.

End Stream_Properties.

End Streams.

Section Map.
Variables A B : Type.
Variable f : A -> B.
CoFixpoint map (s:Stream A) : Stream B := Cons (f (hd s)) (map (tl s)).

Lemma Str_nth_tl_map : forall n s, Str_nth_tl n (map s)= map (Str_nth_tl n s).
Proof.
induction n.
reflexivity.
simpl.
intros s.
apply IHn.
Qed.

Lemma Str_nth_map : forall n s, Str_nth n (map s)= f (Str_nth n s).
Proof.
intros n s.
unfold Str_nth.
rewrite Str_nth_tl_map.
reflexivity.
Qed.

Lemma ForAll_map : forall (P:Stream B -> Prop) (S:Stream A), ForAll (fun s => P
(map s)) S <-> ForAll P (map S).
Proof.
intros P S.
split; generalize S; clear S; cofix ForAll_map; intros S; constructor;
destruct H as [H0 H]; firstorder.
Qed.

Lemma Exists_map : forall (P:Stream B -> Prop) (S:Stream A), Exists (fun s => P
(map s)) S -> Exists P (map S).
Proof.
intros P S H.
(induction H;[left|right]); firstorder.
Defined.

End Map.

Section Constant_Stream.
Variable A : Type.
Variable a : A.
CoFixpoint const  : Stream A := Cons a const.
End Constant_Stream.

Section Zip.

Variable A B C : Type.
Variable f: A -> B -> C.

CoFixpoint zipWith (a:Stream A) (b:Stream B) : Stream C :=
Cons (f (hd a) (hd b)) (zipWith (tl a) (tl b)).

Lemma Str_nth_tl_zipWith : forall n (a:Stream A) (b:Stream B),
 Str_nth_tl n (zipWith a b)= zipWith (Str_nth_tl n a) (Str_nth_tl n b).
Proof.
induction n.
reflexivity.
intros [x xs] [y ys].
unfold Str_nth in *.
simpl in *.
apply IHn.
Qed.

Lemma Str_nth_zipWith : forall n (a:Stream A) (b:Stream B), Str_nth n (zipWith a
 b)= f (Str_nth n a) (Str_nth n b).
Proof.
intros.
unfold Str_nth.
rewrite Str_nth_tl_zipWith.
reflexivity.
Qed.

End Zip.

Unset Implicit Arguments.
