(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(** Basic specifications : Sets containing logical information *)

Require Datatypes.
Require Logic.
Require LogicSyntax.

Section Subsets.

 (** [(sig A P)], or more suggestively [{x:A | (P x)}], denotes the subset 
     of elements of the Set [A] which satisfy the predicate [P].
     Similarly [(sig2 A P Q)], or [{x:A | (P x) & (Q x)}], denotes the subset 
     of elements of the Set [A] which satisfy both [P] and [Q]. *)

  Inductive sig [A:Set;P:A->Prop] : Set
      := exist : (x:A)(P x) -> (sig A P).

  Inductive sig2 [A:Set;P,Q:A->Prop] : Set
      := exist2 : (x:A)(P x) -> (Q x) -> (sig2 A P Q).

 (** [(sigS A P)], or more suggestively [{x:A & (P x)}], is a subtle variant
     of subset where [P] is now of type [Set].
     Similarly for [(sigS2 A P Q)], also written [{x:A & (P x) & (Q x)}]. *)
     
  Inductive sigS [A:Set;P:A->Set] : Set
      := existS : (x:A)(P x) -> (sigS A P).

  Inductive sigS2 [A:Set;P,Q:A->Set] : Set
      := existS2 : (x:A)(P x) -> (Q x) -> (sigS2 A P Q).

End Subsets.

Add Printing Let sig.
Add Printing Let sig2.
Add Printing Let sigS.
Add Printing Let sigS2.


(** Projections of sig *)

Section Subset_projections.

  Variable A:Set.
  Variable P:A->Prop.

  Definition proj1_sig :=
   [e:(sig A P)]Cases e of (exist a b) => a  end.

  Definition proj2_sig :=
   [e:(sig A P)]
     <[e:(sig A P)](P (proj1_sig e))>Cases e of (exist a b) => b  end.

End Subset_projections.


(** Projections of sigS *)

Section Projections.

  Variable A:Set.
  Variable P:A->Set.

 (** An element [y] of a subset [{x:A & (P x)}] is the pair of an [a] of 
     type [A] and of a proof [h] that [a] satisfies [P].
     Then [(projS1 y)] is the witness [a]
     and [(projS2 y)] is the proof of [(P a)] *)

  Definition projS1 (* : (A:Set)(P:A->Set)(sigS A P) -> A *)
           := [x:(sigS A P)]Cases x of (existS a _) => a end.
  Definition projS2 (* : (A:Set)(P:A->Set)(H:(sigS A P))(P (projS1 A P H)) *)
           := [x:(sigS A P)]<[x:(sigS A P)](P (projS1 x))> 
                  Cases x of (existS _ h) => h end.

End Projections.


Section Extended_booleans.

  (** Syntax sumbool ["{_}+{_}"]. *)
  Inductive sumbool [A,B:Prop] : Set
      := left  : A -> (sumbool A B) 
       | right : B -> (sumbool A B).

  (** Syntax sumor ["_+{_}"]. *)
  Inductive sumor [A:Set;B:Prop] : Set
      := inleft  : A -> (sumor A B) 
       | inright : B -> (sumor A B).


End Extended_booleans.


(** Choice *)

Section Choice_lemmas.

  (** The following lemmas state various forms of the axiom of choice *)

  Variables S,S':Set.
  Variable R:S->S'->Prop.
  Variable R':S->S'->Set.
  Variables R1,R2 :S->Prop.

  Lemma Choice : ((x:S)(sig ? [y:S'](R x y))) ->
                     (sig ? [f:S->S'](z:S)(R z (f z))).
  Proof.
   Intro H.
   Exists [z:S]Cases (H z) of (exist y _) => y end.
   Intro z; Elim (H z); Trivial.
  Qed.

  Lemma Choice2 : ((x:S)(sigS ? [y:S'](R' x y))) ->
                     (sigS ? [f:S->S'](z:S)(R' z (f z))).
  Proof.
    Intro H.
    Exists [z:S]Cases (H z) of (existS y _) => y end.
    Intro z; Elim (H z); Trivial.
  Qed.

  Lemma bool_choice : 
    ((x:S)(sumbool (R1 x) (R2 x))) ->
    (sig ? [f:S->bool] (x:S)( ((f x)=true  /\ (R1 x)) 
                           \/ ((f x)=false /\ (R2 x)))).
  Proof.
    Intro H.
    Exists [z:S]Cases (H z) of (left _) => true | (right _) => false end.
    Intro z; Elim (H z); Auto.
  Qed.

End Choice_lemmas.

 (** A result of type [(Exc A)] is either a normal value of type [A] or 
     an [error] :
     [Inductive Exc [A:Set] : Set := value : A->(Exc A) | error : (Exc A)]
     it is implemented using the option type. *) 

Definition Exc := option.
Definition value := Some.
Definition error := None.

Definition except := False_rec. (* for compatibility with previous versions *)

Theorem absurd_set : (A:Prop)(C:Set)A->(~A)->C.
Proof.
  Intros A C h1 h2.
  Apply False_rec.
  Apply (h2 h1).
Qed.

Hints Resolve left right inleft inright : core v62.

(** Sigma Type at Type level [sigT] *)

Inductive sigT [A:Type;P:A->Type] : Type
    := existT : (x:A)(P x) -> (sigT A P).

Section projections_sigT.

  Variable A:Type.
  Variable P:A->Type.

  Definition projT1 (* : (A:Type)(P:A->Type)(sigT A P) -> A *)
              := [H:(sigT A P)]Cases H of (existT x _) => x end.
   
  Definition projT2 (* : (A:Type)(P:A->Type)(p:(sigT A P))(P (projT1 A P p)) *)
              := [H:(sigT A P)]<[H:(sigT A P)](P (projT1 H))> 
                     Cases H of (existT x h) => h end.

End projections_sigT.
