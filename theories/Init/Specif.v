(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Set Implicit Arguments.

(** Basic specifications : Sets containing logical information *)

Require Import Notations.
Require Import Datatypes.
Require Import Logic.

(** Subsets *)

(** [(sig A P)], or more suggestively [{x:A | (P x)}], denotes the subset 
    of elements of the Set [A] which satisfy the predicate [P].
    Similarly [(sig2 A P Q)], or [{x:A | (P x) & (Q x)}], denotes the subset 
    of elements of the Set [A] which satisfy both [P] and [Q]. *)

Inductive sig (A:Set) (P:A -> Prop) : Set :=
    exist : forall x:A, P x -> sig (A:=A) P.

Inductive sig2 (A:Set) (P Q:A -> Prop) : Set :=
    exist2 : forall x:A, P x -> Q x -> sig2 (A:=A) P Q.

(** [(sigS A P)], or more suggestively [{x:A & (P x)}], is a subtle variant
    of subset where [P] is now of type [Set].
    Similarly for [(sigS2 A P Q)], also written [{x:A & (P x) & (Q x)}]. *)
     
Inductive sigS (A:Set) (P:A -> Set) : Set :=
    existS : forall x:A, P x -> sigS (A:=A) P.

Inductive sigS2 (A:Set) (P Q:A -> Set) : Set :=
    existS2 : forall x:A, P x -> Q x -> sigS2 (A:=A) P Q.

Arguments Scope sig [type_scope type_scope].
Arguments Scope sig2 [type_scope type_scope type_scope].
Arguments Scope sigS [type_scope type_scope].
Arguments Scope sigS2 [type_scope type_scope type_scope].

Notation "{ x : A  |  P }" := (sig (fun x:A => P)) : type_scope.
Notation "{ x : A  |  P  &  Q }" := (sig2 (fun x:A => P) (fun x:A => Q)) :
  type_scope.
Notation "{ x : A  &  P }" := (sigS (fun x:A => P)) : type_scope.
Notation "{ x : A  &  P  &  Q }" := (sigS2 (fun x:A => P) (fun x:A => Q)) :
  type_scope.

Add Printing Let sig.
Add Printing Let sig2.
Add Printing Let sigS.
Add Printing Let sigS2.


(** Projections of sig *)

Section Subset_projections.

  Variable A : Set.
  Variable P : A -> Prop.

  Definition proj1_sig (e:sig P) := match e with
                                    | exist a b => a
                                    end.

  Definition proj2_sig (e:sig P) :=
    match e return P (proj1_sig e) with
    | exist a b => b
    end.

End Subset_projections.


(** Projections of sigS *)

Section Projections.

  Variable A : Set.
  Variable P : A -> Set.

 (** An element [y] of a subset [{x:A & (P x)}] is the pair of an [a] of 
     type [A] and of a proof [h] that [a] satisfies [P].
     Then [(projS1 y)] is the witness [a]
     and [(projS2 y)] is the proof of [(P a)] *)

  Definition projS1 (x:sigS P) : A := match x with
                                      | existS a _ => a
                                      end.
  Definition projS2 (x:sigS P) : P (projS1 x) :=
    match x return P (projS1 x) with
    | existS _ h => h
    end.

End Projections.


(** Extended_booleans *)

Inductive sumbool (A B:Prop) : Set :=
  | left : A -> {A} + {B}
  | right : B -> {A} + {B} 
 where "{ A } + { B }" := (sumbool A B) : type_scope.

Add Printing If sumbool.

Inductive sumor (A:Set) (B:Prop) : Set :=
  | inleft : A -> A + {B}
  | inright : B -> A + {B} 
 where "A + { B }" := (sumor A B) : type_scope.

Add Printing If sumor.

(** Choice *)

Section Choice_lemmas.

  (** The following lemmas state various forms of the axiom of choice *)

  Variables S S' : Set.
  Variable R : S -> S' -> Prop.
  Variable R' : S -> S' -> Set.
  Variables R1 R2 : S -> Prop.

  Lemma Choice :
   (forall x:S, sig (fun y:S' => R x y)) ->
   sig (fun f:S -> S' => forall z:S, R z (f z)).
  Proof.
   intro H.
   exists (fun z:S => match H z with
                      | exist y _ => y
                      end).
   intro z; destruct (H z); trivial.
  Qed.

  Lemma Choice2 :
   (forall x:S, sigS (fun y:S' => R' x y)) ->
   sigS (fun f:S -> S' => forall z:S, R' z (f z)).
  Proof.
    intro H.
    exists (fun z:S => match H z with
                       | existS y _ => y
                       end).
    intro z; destruct (H z); trivial.
  Qed.

  Lemma bool_choice :
   (forall x:S, {R1 x} + {R2 x}) ->
   sig
     (fun f:S -> bool =>
        forall x:S, f x = true /\ R1 x \/ f x = false /\ R2 x).
  Proof.
    intro H.
    exists
     (fun z:S => match H z with
                 | left _ => true
                 | right _ => false
                 end).
    intro z; destruct (H z); auto.
  Qed.

End Choice_lemmas.

 (** A result of type [(Exc A)] is either a normal value of type [A] or 
     an [error] :
     [Inductive Exc [A:Set] : Set := value : A->(Exc A) | error : (Exc A)]
     it is implemented using the option type. *) 

Definition Exc := option.
Definition value := Some.
Definition error := @None.

Implicit Arguments error [A].

Definition except := False_rec. (* for compatibility with previous versions *)

Implicit Arguments except [P].

Theorem absurd_set : forall (A:Prop) (C:Set), A -> ~ A -> C.
Proof.
  intros A C h1 h2.
  apply False_rec.
  apply (h2 h1).
Qed.

Hint Resolve left right inleft inright: core v62.

(** Sigma Type at Type level [sigT] *)

Inductive sigT (A:Type) (P:A -> Type) : Type :=
    existT : forall x:A, P x -> sigT (A:=A) P.

Section projections_sigT.

  Variable A : Type.
  Variable P : A -> Type.

  Definition projT1 (H:sigT P) : A := match H with
                                      | existT x _ => x
                                      end.
   
  Definition projT2 : forall x:sigT P, P (projT1 x) :=
    fun H:sigT P => match H return P (projT1 H) with
                    | existT x h => h
                    end.

End projections_sigT.

