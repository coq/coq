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

CoInductive Set Stream   := Cons : A->Stream->Stream.


Definition hd  := 
  [x:Stream] Cases x of (Cons a _) => a end.

Definition tl  := 
  [x:Stream] Cases x of (Cons _ s) => s end.


Fixpoint Str_nth_tl [n:nat] : Stream->Stream := 
  [s:Stream] Cases n of
	          O    => s
		|(S m) => (Str_nth_tl m (tl s))
	    end.

Definition Str_nth : nat->Stream->A := [n:nat][s:Stream](hd (Str_nth_tl n s)).


Lemma unfold_Stream :(x:Stream)x=(Cases x of (Cons a s) => (Cons a s) end). 
Proof.
  Intro x.
  Case x.
  Trivial.
Qed.

Lemma tl_nth_tl : (n:nat)(s:Stream)(tl (Str_nth_tl n s))=(Str_nth_tl n (tl s)).
Proof.
  Induction n; Simpl; Auto.
Qed.
Hints Resolve tl_nth_tl : datatypes v62.

Lemma Str_nth_tl_plus 
: (n,m:nat)(s:Stream)(Str_nth_tl n (Str_nth_tl m s))=(Str_nth_tl (plus n m) s).
Induction n; Simpl; Intros; Auto with datatypes.
Rewrite <- H.
Rewrite tl_nth_tl; Trivial with datatypes.
Qed.

Lemma Str_nth_plus 
  : (n,m:nat)(s:Stream)(Str_nth n (Str_nth_tl m s))=(Str_nth (plus n m) s).
Intros; Unfold Str_nth; Rewrite Str_nth_tl_plus; Trivial with datatypes.
Qed.

(** Extensional Equality between two streams  *)

CoInductive EqSt  : Stream->Stream->Prop := 
	    eqst : (s1,s2:Stream)
		   ((hd s1)=(hd s2))->
		   (EqSt (tl s1) (tl s2))
                    ->(EqSt s1 s2).

(** A coinduction principle *)

Tactic Definition CoInduction proof := 
  Cofix proof; Intros; Constructor;
    [Clear proof | Try (Apply proof;Clear proof)].


(** Extensional equality is an equivalence relation *)

Theorem  EqSt_reflex : (s:Stream)(EqSt s s).
CoInduction EqSt_reflex.
Reflexivity.
Qed.

Theorem sym_EqSt : 
 (s1:Stream)(s2:Stream)(EqSt s1 s2)->(EqSt s2 s1).
(CoInduction Eq_sym).
Case H;Intros;Symmetry;Assumption.
Case H;Intros;Assumption.
Qed.


Theorem trans_EqSt : 
 (s1,s2,s3:Stream)(EqSt s1 s2)->(EqSt s2 s3)->(EqSt s1 s3).
(CoInduction Eq_trans).
Transitivity (hd s2).
Case H; Intros; Assumption.
Case H0; Intros; Assumption.
Apply (Eq_trans (tl s1) (tl s2) (tl s3)).
Case H;  Trivial with datatypes.
Case H0; Trivial with datatypes.
Qed.

(** The definition given is equivalent to require the elements at each
    position to be equal *)

Theorem eqst_ntheq :
  (n:nat)(s1,s2:Stream)(EqSt s1 s2)->(Str_nth n s1)=(Str_nth n s2).
Unfold Str_nth; Induction n.
Intros s1 s2 H; Case H; Trivial with datatypes.
Intros m hypind.
Simpl.
Intros s1 s2 H.
Apply hypind.
Case H; Trivial with datatypes.
Qed.

Theorem ntheq_eqst : 
  (s1,s2:Stream)((n:nat)(Str_nth n s1)=(Str_nth n s2))->(EqSt s1 s2).
(CoInduction Equiv2).
Apply (H O).
Intros n; Apply (H (S n)).
Qed.

Section Stream_Properties.

Variable P : Stream->Prop.

(*i
Inductive Exists : Stream -> Prop :=
  | Here    : forall x:Stream, P x -> Exists x
  | Further : forall x:Stream, ~ P x -> Exists (tl x) -> Exists x.
i*)

Inductive   Exists :  Stream -> Prop :=
   Here    : (x:Stream)(P x) ->(Exists x) |
   Further : (x:Stream)(Exists (tl x))->(Exists x).

CoInductive ForAll : Stream  -> Prop :=
    forall : (x:Stream)(P x)->(ForAll (tl x))->(ForAll x).


Section Co_Induction_ForAll.
Variable   Inv        :  Stream -> Prop.
Hypothesis InvThenP   : (x:Stream)(Inv x)->(P x).
Hypothesis InvIsStable: (x:Stream)(Inv x)->(Inv (tl x)).

Theorem ForAll_coind : (x:Stream)(Inv x)->(ForAll x).
(CoInduction ForAll_coind);Auto.
Qed.
End Co_Induction_ForAll.

End Stream_Properties.

End Streams.

Section Map.
Variables A,B : Set.
Variable  f   : A->B.
CoFixpoint map : (Stream A)->(Stream B) :=
 [s:(Stream A)](Cons (f (hd s)) (map (tl s))).
End Map.

Section Constant_Stream.
Variable A : Set.
Variable a : A.
CoFixpoint const : (Stream A) := (Cons a const).
End Constant_Stream.

Unset Implicit Arguments.
