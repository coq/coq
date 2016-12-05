(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Basic specifications : sets that may contain logical information *)

Set Implicit Arguments.
Set Reversible Pattern Implicit.

Require Import Notations.
Require Import Datatypes.
Require Import Logic.

(** Subsets and Sigma-types *)

(** [(sig A P)], or more suggestively [{x:A | P x}], denotes the subset
    of elements of the type [A] which satisfy the predicate [P].
    Similarly [(sig2 A P Q)], or [{x:A | P x & Q x}], denotes the subset
    of elements of the type [A] which satisfy both [P] and [Q]. *)

Inductive sig (A:Type) (P:A -> Prop) : Type :=
    exist : forall x:A, P x -> sig P.

Inductive sig2 (A:Type) (P Q:A -> Prop) : Type :=
    exist2 : forall x:A, P x -> Q x -> sig2 P Q.

(** [(sigT A P)], or more suggestively [{x:A & (P x)}] is a Sigma-type.
    Similarly for [(sigT2 A P Q)], also written [{x:A & (P x) & (Q x)}]. *)

Inductive sigT (A:Type) (P:A -> Type) : Type :=
    existT : forall x:A, P x -> sigT P.

Inductive sigT2 (A:Type) (P Q:A -> Type) : Type :=
    existT2 : forall x:A, P x -> Q x -> sigT2 P Q.

(* Notations *)

Arguments sig (A P)%type.
Arguments sig2 (A P Q)%type.
Arguments sigT (A P)%type.
Arguments sigT2 (A P Q)%type.

Notation "{ x  |  P }" := (sig (fun x => P)) : type_scope.
Notation "{ x  |  P  & Q }" := (sig2 (fun x => P) (fun x => Q)) : type_scope.
Notation "{ x : A  |  P }" := (sig (A:=A) (fun x => P)) : type_scope.
Notation "{ x : A  |  P  & Q }" := (sig2 (A:=A) (fun x => P) (fun x => Q)) :
  type_scope.
Notation "{ x : A  & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
Notation "{ x : A  & P  & Q }" := (sigT2 (A:=A) (fun x => P) (fun x => Q)) :
  type_scope.

Add Printing Let sig.
Add Printing Let sig2.
Add Printing Let sigT.
Add Printing Let sigT2.


(** Projections of [sig]

    An element [y] of a subset [{x:A | (P x)}] is the pair of an [a]
    of type [A] and of a proof [h] that [a] satisfies [P].  Then
    [(proj1_sig y)] is the witness [a] and [(proj2_sig y)] is the
    proof of [(P a)] *)

(* Set Universe Polymorphism. *)
Section Subset_projections.

  Variable A : Type.
  Variable P : A -> Prop.

  Definition proj1_sig (e:sig P) := match e with
                                    | exist _ a b => a
                                    end.

  Definition proj2_sig (e:sig P) :=
    match e return P (proj1_sig e) with
    | exist _ a b => b
    end.

End Subset_projections.


(** [sig2] of a predicate can be projected to a [sig].

    This allows [proj1_sig] and [proj2_sig] to be usable with [sig2].

    The [let] statements occur in the body of the [exist] so that
    [proj1_sig] of a coerced [X : sig2 P Q] will unify with [let (a,
    _, _) := X in a] *)

Definition sig_of_sig2 (A : Type) (P Q : A -> Prop) (X : sig2 P Q) : sig P
  := exist P
           (let (a, _, _) := X in a)
           (let (x, p, _) as s return (P (let (a, _, _) := s in a)) := X in p).

(** Projections of [sig2]

    An element [y] of a subset [{x:A | (P x) & (Q x)}] is the triple
    of an [a] of type [A], a of a proof [h] that [a] satisfies [P],
    and a proof [h'] that [a] satisfies [Q].  Then
    [(proj1_sig (sig_of_sig2 y))] is the witness [a],
    [(proj2_sig (sig_of_sig2 y))] is the proof of [(P a)], and
    [(proj3_sig y)] is the proof of [(Q a)]. *)

Section Subset_projections2.

  Variable A : Type.
  Variables P Q : A -> Prop.

  Definition proj3_sig (e : sig2 P Q) :=
    let (a, b, c) return Q (proj1_sig (sig_of_sig2 e)) := e in c.

End Subset_projections2.


(** Projections of [sigT]

    An element [x] of a sigma-type [{y:A & P y}] is a dependent pair
    made of an [a] of type [A] and an [h] of type [P a].  Then,
    [(projT1 x)] is the first projection and [(projT2 x)] is the
    second projection, the type of which depends on the [projT1]. *)



Section Projections.

  Variable A : Type.
  Variable P : A -> Type.

  Definition projT1 (x:sigT P) : A := match x with
                                      | existT _ a _ => a
                                      end.

  Definition projT2 (x:sigT P) : P (projT1 x) :=
    match x return P (projT1 x) with
    | existT _ _ h => h
    end.

End Projections.

(** [sigT2] of a predicate can be projected to a [sigT].

    This allows [projT1] and [projT2] to be usable with [sigT2].

    The [let] statements occur in the body of the [existT] so that
    [projT1] of a coerced [X : sigT2 P Q] will unify with [let (a,
    _, _) := X in a] *)

Definition sigT_of_sigT2 (A : Type) (P Q : A -> Type) (X : sigT2 P Q) : sigT P
  := existT P
            (let (a, _, _) := X in a)
            (let (x, p, _) as s return (P (let (a, _, _) := s in a)) := X in p).

(** Projections of [sigT2]

    An element [x] of a sigma-type [{y:A & P y & Q y}] is a dependent
    pair made of an [a] of type [A], an [h] of type [P a], and an [h']
    of type [Q a].  Then, [(projT1 (sigT_of_sigT2 x))] is the first
    projection, [(projT2 (sigT_of_sigT2 x))] is the second projection,
    and [(projT3 x)] is the third projection, the types of which
    depends on the [projT1]. *)

Section Projections2.

  Variable A : Type.
  Variables P Q : A -> Type.

  Definition projT3 (e : sigT2 P Q) :=
    let (a, b, c) return Q (projT1 (sigT_of_sigT2 e)) := e in c.

End Projections2.

(** [sigT] of a predicate is equivalent to [sig] *)

Definition sig_of_sigT (A : Type) (P : A -> Prop) (X : sigT P) : sig P
  := exist P (projT1 X) (projT2 X).

Definition sigT_of_sig (A : Type) (P : A -> Prop) (X : sig P) : sigT P
  := existT P (proj1_sig X) (proj2_sig X).

(** [sigT2] of a predicate is equivalent to [sig2] *)

Definition sig2_of_sigT2 (A : Type) (P Q : A -> Prop) (X : sigT2 P Q) : sig2 P Q
  := exist2 P Q (projT1 (sigT_of_sigT2 X)) (projT2 (sigT_of_sigT2 X)) (projT3 X).

Definition sigT2_of_sig2 (A : Type) (P Q : A -> Prop) (X : sig2 P Q) : sigT2 P Q
  := existT2 P Q (proj1_sig (sig_of_sig2 X)) (proj2_sig (sig_of_sig2 X)) (proj3_sig X).

(** η Principles *)
Definition sigT_eta {A P} (p : { a : A & P a })
  : p = existT _ (projT1 p) (projT2 p).
Proof. destruct p; reflexivity. Defined.

Definition sig_eta {A P} (p : { a : A | P a })
  : p = exist _ (proj1_sig p) (proj2_sig p).
Proof. destruct p; reflexivity. Defined.

Definition sigT2_eta {A P Q} (p : { a : A & P a & Q a })
  : p = existT2 _ _ (projT1 (sigT_of_sigT2 p)) (projT2 (sigT_of_sigT2 p)) (projT3 p).
Proof. destruct p; reflexivity. Defined.

Definition sig2_eta {A P Q} (p : { a : A | P a & Q a })
  : p = exist2 _ _ (proj1_sig (sig_of_sig2 p)) (proj2_sig (sig_of_sig2 p)) (proj3_sig p).
Proof. destruct p; reflexivity. Defined.

(** [exists x : A, B] is equivalent to [inhabited {x : A | B}] *)
Lemma exists_to_inhabited_sig {A P} : (exists x : A, P x) -> inhabited {x : A | P x}.
Proof.
  intros [x y]. exact (inhabits (exist _ x y)).
Qed.

Lemma inhabited_sig_to_exists {A P} : inhabited {x : A | P x} -> exists x : A, P x.
Proof.
  intros [[x y]];exists x;exact y.
Qed.

(** Equality of sigma types *)
Import EqNotations.

(** Equality for [sigT] *)
Section sigT.
  Local Unset Implicit Arguments.
  (** Projecting an equality of a pair to equality of the first components *)
  Definition projT1_eq {A} {P : A -> Type} {u v : sigT P} (p : u = v)
  : projT1 u = projT1 v
    := f_equal (@projT1 _ _) p.

  (** Projecting an equality of a pair to equality of the second components *)
  Definition projT2_eq {A} {P : A -> Type} {u v : sigT P} (p : u = v)
  : rew projT1_eq p in projT2 u = projT2 v.
  Proof.
    destruct p; reflexivity.
  Defined.

  (** Equality of [sigT] is itself a [sigT] *)
  Definition eq_sigT_uncurried {A : Type} {P : A -> Type} (u v : sigT P)
             (pq : sigT (fun p : projT1 u = projT1 v => rew p in projT2 u = projT2 v))
  : u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; simpl in *.
    destruct pq as [p q].
    destruct q; simpl in *.
    destruct p; reflexivity.
  Defined.

  (** Curried version of proving equality of sigma types *)
  Definition eq_sigT {A : Type} {P : A -> Type} (u v : sigT P)
             (p : projT1 u = projT1 v) (q : rew p in projT2 u = projT2 v)
  : u = v
    := eq_sigT_uncurried u v (existT _ p q).

  (** Equality of [sigT] when the property is an hProp *)
  Definition eq_sigT_hprop {A P} (P_hprop : forall (x : A) (p q : P x), p = q)
             (u v : @sigT A P)
             (p : projT1 u = projT1 v)
    : u = v
    := eq_sigT u v p (P_hprop _ _ _).

  (** Equivalence of equality of [sigT] with a [sigT] of equality *)
  (** We could actually use [IsIso] here, but for simplicity, we
      don't.  If we wanted to deal with proofs of equality of Σ types
      in dependent positions, we'd need it. *)
  Definition eq_sigT_uncurried_iff {A P}
             (u v : @sigT A P)
    : u = v <-> (sigT (fun p : projT1 u = projT1 v => rew p in projT2 u = projT2 v)).
  Proof.
    split; [ intro; subst; exists eq_refl; reflexivity | apply eq_sigT_uncurried ].
  Defined.

  (** Induction principle for [@eq (sigT _)] *)
  Definition eq_sigT_rect {A P} {u v : @sigT A P} (Q : u = v -> Type)
             (f : forall p q, Q (eq_sigT u v p q))
    : forall p, Q p.
  Proof. intro p; specialize (f (projT1_eq p) (projT2_eq p)); destruct u, p; exact f. Defined.
  Definition eq_sigT_rec {A P u v} (Q : u = v :> @sigT A P -> Set) := eq_sigT_rect Q.
  Definition eq_sigT_ind {A P u v} (Q : u = v :> @sigT A P -> Prop) := eq_sigT_rec Q.

  (** Equivalence of equality of [sigT] involving hProps with equality of the first components *)
  Definition eq_sigT_hprop_iff {A P} (P_hprop : forall (x : A) (p q : P x), p = q)
             (u v : @sigT A P)
    : u = v <-> (projT1 u = projT1 v)
    := conj (fun p => f_equal (@projT1 _ _) p) (eq_sigT_hprop P_hprop u v).

  (** Non-dependent classification of equality of [sigT] *)
  Definition eq_sigT_nondep {A B : Type} (u v : @sigT A (fun _ => B))
             (p : projT1 u = projT1 v) (q : projT2 u = projT2 v)
  : u = v
    := @eq_sigT _ _ u v p (eq_trans (eq_rect_const _ _) q).

  (** Classification of transporting across an equality of [sigT]s *)
  Lemma eq_rect_sigT {A x} {P : A -> Type} (Q : forall a, P a -> Prop) (u : sigT (Q x)) {y} (H : x = y)
  : rew [fun a => sigT (Q a)] H in u
    = existT
        (Q y)
        (rew H in projT1 u)
        match H in (_ = y) return Q y (rew H in projT1 u) with
          | eq_refl => projT2 u
        end.
  Proof.
    destruct H, u; reflexivity.
  Defined.
End sigT.

(** Equality for [sig] *)
Section sig.
  Local Unset Implicit Arguments.
  Definition proj1_sig_eq {A} {P : A -> Prop} {u v : sig P} (p : u = v)
  : proj1_sig u = proj1_sig v
    := f_equal (@proj1_sig _ _) p.

  Definition proj2_sig_eq {A} {P : A -> Prop} {u v : sig P} (p : u = v)
  : rew proj1_sig_eq p in proj2_sig u = proj2_sig v.
  Proof.
    destruct p; reflexivity.
  Defined.

  Definition eq_sig_uncurried {A : Type} {P : A -> Prop} (u v : sig P)
             (pq : {p : proj1_sig u = proj1_sig v | rew p in proj2_sig u = proj2_sig v})
  : u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; simpl in *.
    destruct pq as [p q].
    destruct q; simpl in *.
    destruct p; reflexivity.
  Defined.

  Definition eq_sig {A : Type} {P : A -> Prop} (u v : sig P)
             (p : proj1_sig u = proj1_sig v) (q : rew p in proj2_sig u = proj2_sig v)
  : u = v
    := eq_sig_uncurried u v (exist _ p q).

  Definition eq_sig_rect {A P} {u v : @sig A P} (Q : u = v -> Type)
             (f : forall p q, Q (eq_sig u v p q))
    : forall p, Q p.
  Proof. intro p; specialize (f (proj1_sig_eq p) (proj2_sig_eq p)); destruct u, p; exact f. Defined.
  Definition eq_sig_rec {A P u v} (Q : u = v :> @sig A P -> Set) := eq_sig_rect Q.
  Definition eq_sig_ind {A P u v} (Q : u = v :> @sig A P -> Prop) := eq_sig_rec Q.

  Definition eq_sig_hprop {A} {P : A -> Prop} (P_hprop : forall (x : A) (p q : P x), p = q)
             (u v : @sig A P)
             (p : proj1_sig u = proj1_sig v)
    : u = v
    := eq_sig u v p (P_hprop _ _ _).

  Definition eq_sig_uncurried_iff {A} {P : A -> Prop}
             (u v : @sig A P)
    : u = v <-> (sig (fun p : proj1_sig u = proj1_sig v => rew p in proj2_sig u = proj2_sig v)).
  Proof.
    split; [ intro; subst; exists eq_refl; reflexivity | apply eq_sig_uncurried ].
  Defined.

  Definition eq_sig_hprop_iff {A} {P : A -> Prop} (P_hprop : forall (x : A) (p q : P x), p = q)
             (u v : @sig A P)
    : u = v <-> (proj1_sig u = proj1_sig v)
    := conj (fun p => f_equal (@proj1_sig _ _) p) (eq_sig_hprop P_hprop u v).

  Lemma eq_rect_sig {A x} {P : A -> Type} (Q : forall a, P a -> Prop) (u : sig (Q x)) {y} (H : x = y)
  : rew [fun a => sig (Q a)] H in u
    = exist
        (Q y)
        (rew H in proj1_sig u)
        match H in (_ = y) return Q y (rew H in proj1_sig u) with
          | eq_refl => proj2_sig u
        end.
  Proof.
    destruct H, u; reflexivity.
  Defined.
End sig.


(** [sumbool] is a boolean type equipped with the justification of
    their value *)

Inductive sumbool (A B:Prop) : Set :=
  | left : A -> {A} + {B}
  | right : B -> {A} + {B}
 where "{ A } + { B }" := (sumbool A B) : type_scope.

Add Printing If sumbool.

Arguments left {A B} _, [A] B _.
Arguments right {A B} _ , A [B] _.

(** [sumor] is an option type equipped with the justification of why
    it may not be a regular value *)

Inductive sumor (A:Type) (B:Prop) : Type :=
  | inleft : A -> A + {B}
  | inright : B -> A + {B}
 where "A + { B }" := (sumor A B) : type_scope.

Add Printing If sumor.

Arguments inleft {A B} _ , [A] B _.
Arguments inright {A B} _ , A [B] _.

(* Unset Universe Polymorphism. *)

(** Various forms of the axiom of choice for specifications *)

Section Choice_lemmas.

  Variables S S' : Set.
  Variable R : S -> S' -> Prop.
  Variable R' : S -> S' -> Set.
  Variables R1 R2 : S -> Prop.

  Lemma Choice :
   (forall x:S, {y:S' | R x y}) -> {f:S -> S' | forall z:S, R z (f z)}.
  Proof.
   intro H.
   exists (fun z => proj1_sig (H z)).
   intro z; destruct (H z); assumption.
  Defined.

  Lemma Choice2 :
   (forall x:S, {y:S' & R' x y}) -> {f:S -> S' & forall z:S, R' z (f z)}.
  Proof.
    intro H.
    exists (fun z => projT1 (H z)).
    intro z; destruct (H z); assumption.
  Defined.

  Lemma bool_choice :
   (forall x:S, {R1 x} + {R2 x}) ->
     {f:S -> bool | forall x:S, f x = true /\ R1 x \/ f x = false /\ R2 x}.
  Proof.
    intro H.
    exists (fun z:S => if H z then true else false).
    intro z; destruct (H z); auto.
  Defined.

End Choice_lemmas.

Section Dependent_choice_lemmas.

  Variables X : Set.
  Variable R : X -> X -> Prop.

  Lemma dependent_choice :
    (forall x:X, {y | R x y}) ->
    forall x0, {f : nat -> X | f O = x0 /\ forall n, R (f n) (f (S n))}.
  Proof.
    intros H x0.
    set (f:=fix f n := match n with O => x0 | S n' => proj1_sig (H (f n')) end).
    exists f.
    split. reflexivity.
    induction n; simpl; apply proj2_sig.
  Defined.

End Dependent_choice_lemmas.


 (** A result of type [(Exc A)] is either a normal value of type [A] or
     an [error] :

     [Inductive Exc [A:Type] : Type := value : A->(Exc A) | error : (Exc A)].

     It is implemented using the option type. *)
Section Exc.
  Variable A : Type.

  Definition Exc := option A.
  Definition value := @Some A.
  Definition error := @None A.
End Exc.
Arguments error {A}.

Definition except := False_rec. (* for compatibility with previous versions *)

Arguments except [P] _.

Theorem absurd_set : forall (A:Prop) (C:Set), A -> ~ A -> C.
Proof.
  intros A C h1 h2.
  apply False_rec.
  apply (h2 h1).
Defined.

Hint Resolve left right inleft inright: core.
Hint Resolve exist exist2 existT existT2: core.

(* Compatibility *)

Notation sigS := sigT (compat "8.2").
Notation existS := existT (compat "8.2").
Notation sigS_rect := sigT_rect (compat "8.2").
Notation sigS_rec := sigT_rec (compat "8.2").
Notation sigS_ind := sigT_ind (compat "8.2").
Notation projS1 := projT1 (compat "8.2").
Notation projS2 := projT2 (compat "8.2").

Notation sigS2 := sigT2 (compat "8.2").
Notation existS2 := existT2 (compat "8.2").
Notation sigS2_rect := sigT2_rect (compat "8.2").
Notation sigS2_rec := sigT2_rec (compat "8.2").
Notation sigS2_ind := sigT2_ind (compat "8.2").
