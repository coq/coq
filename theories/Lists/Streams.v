(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Set Implicit Arguments.

(** Streams *)

Section Streams.

Variable A : Set.

CoInductive Stream : Set :=
    Cons : A -> Stream -> Stream.


Definition hd (x:Stream) := match x with
                            | Cons a _ => a
                            end.

Definition tl (x:Stream) := match x with
                            | Cons _ s => s
                            end.


Fixpoint Str_nth_tl (n:nat) (s:Stream) {struct n} : Stream :=
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
  simple induction n; simpl in |- *; auto.
Qed.
Hint Resolve tl_nth_tl: datatypes v62.

Lemma Str_nth_tl_plus :
 forall (n m:nat) (s:Stream),
   Str_nth_tl n (Str_nth_tl m s) = Str_nth_tl (n + m) s.
simple induction n; simpl in |- *; intros; auto with datatypes.
rewrite <- H.
rewrite tl_nth_tl; trivial with datatypes.
Qed.

Lemma Str_nth_plus :
 forall (n m:nat) (s:Stream), Str_nth n (Str_nth_tl m s) = Str_nth (n + m) s.
intros; unfold Str_nth in |- *; rewrite Str_nth_tl_plus;
 trivial with datatypes.
Qed.

(** Extensional Equality between two streams  *)

CoInductive EqSt : Stream -> Stream -> Prop :=
    eqst :
      forall s1 s2:Stream,
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
case H; intros; symmetry  in |- *; assumption.
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
unfold Str_nth in |- *; simple induction n.
intros s1 s2 H; case H; trivial with datatypes.
intros m hypind.
simpl in |- *.
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

Inductive Exists : Stream -> Prop :=
  | Here : forall x:Stream, P x -> Exists x
  | Further : forall x:Stream, Exists (tl x) -> Exists x.

CoInductive ForAll : Stream -> Prop :=
    HereAndFurther : forall x:Stream, P x -> ForAll (tl x) -> ForAll x.


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
Variables A B : Set.
Variable f : A -> B.
CoFixpoint map (s:Stream A) : Stream B := Cons (f (hd s)) (map (tl s)).
End Map.

Section Constant_Stream.
Variable A : Set.
Variable a : A.
CoFixpoint const  : Stream A := Cons a const.
End Constant_Stream.

Unset Implicit Arguments.