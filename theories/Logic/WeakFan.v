(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** A constructive proof of a non-standard version of the weak Fan Theorem
    in the formulation of which infinite paths are treated as
    predicates. The representation of paths as relations avoid the
    need for classical logic and unique choice. The idea of the proof
    comes from the proof of the weak König's lemma from separation in
    second-order arithmetic [[Simpson99]].

    [[Simpson99]] Stephen G. Simpson. Subsystems of second order
    arithmetic, Cambridge University Press, 1999 *)

Require Import List.
Import ListNotations.

(** [inductively_barred P l] means that P eventually holds above l *)

Inductive inductively_barred P : list bool -> Prop :=
| now l : P l -> inductively_barred P l
| propagate l :
    inductively_barred P (true::l) ->
    inductively_barred P (false::l) ->
    inductively_barred P l.

(** [approx X l] says that [l] is a boolean representation of a prefix of [X] *)

Fixpoint approx X (l:list bool) :=
  match l with
  | [] => True
  | b::l => approx X l /\ (if b then X (length l) else ~ X (length l))
  end.

(** [barred P] means that for any infinite path represented as a predicate,
    the property [P] holds for some prefix of the path *)

Definition barred P :=
  forall (X:nat -> Prop), exists l, approx X l /\ P l.

(** The proof proceeds by building a set [Y] of finite paths
   approximating either the smallest unbarred infinite path in [P], if
   there is one (taking [true]>[false]), or the path [true::true::...]
   if [P] happens to be inductively_barred *)

Fixpoint Y P (l:list bool) :=
  match l with
  | [] => True
  | b::l =>
      Y P l /\
      if b then inductively_barred P (false::l) else ~ inductively_barred P (false::l)
  end.

Lemma Y_unique : forall P l1 l2, length l1 = length l2 -> Y P l1 -> Y P l2 -> l1 = l2.
Proof.
induction l1, l2.
- trivial.
- discriminate.
- discriminate.
- intros H (HY1,H1) (HY2,H2).
  injection H as H.
  pose proof (IHl1 l2 H HY1 HY2). clear HY1 HY2 H IHl1.
  subst l1.
  f_equal.
  destruct a, b; firstorder.
Qed.

(** [X] is the translation of [Y] as a predicate *)

Definition X P n := exists l, length l = n /\ Y P (true::l).

Lemma Y_approx : forall P l, approx (X P) l -> Y P l.
Proof.
induction l.
- trivial.
- intros (H,Hb). split.
  + auto.
  + unfold X in Hb.
    destruct a.
    * destruct Hb as (l',(Hl',(HYl',HY))).
      rewrite <- (Y_unique P l' l Hl'); auto.
    * firstorder.
Qed.

Theorem WeakFanTheorem : forall P, barred P -> inductively_barred P [].
Proof.
intros P Hbar.
destruct Hbar with (X P) as (l,(Hd%Y_approx,HP)).
assert (inductively_barred P l) by (apply (now P l), HP).
clear Hbar HP.
induction l as [|a l].
- assumption.
- destruct Hd as (Hd,HX).
  apply (IHl Hd). clear IHl.
  destruct a; unfold X in HX; simpl in HX.
  + apply propagate; assumption.
  + exfalso; destruct (HX H).
Qed.
