(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Proofs of specification for functions defined over Vector

   Author: Pierre Boutillier
   Institution: PPS, INRIA 12/2010
*)

Require Fin.
Require Import VectorDef.
Import VectorNotations.

Definition cons_inj {A} {a1 a2} {n} {v1 v2 : t A n}
 (eq : a1 :: v1 = a2 :: v2) : a1 = a2 /\ v1 = v2 :=
   match eq in _ = x return caseS _ (fun a2' _ v2' => fun v1' => a1 = a2' /\ v1' = v2') x v1
   with | eq_refl => conj eq_refl eq_refl
   end.

Lemma eta {A} {n} (v : t A (S n)) : v = hd v :: tl v.
Proof.
intros; apply caseS with (v:=v); intros; reflexivity.
Defined.

(** Lemmas are done for functions that use [Fin.t] but thanks to [Peano_dec.le_unique], all
is true for the one that use [lt] *)

Lemma eq_nth_iff A n (v1 v2: t A n):
  (forall p1 p2, p1 = p2 -> v1 [@ p1 ] = v2 [@ p2 ]) <-> v1 = v2.
Proof.
split.
- revert n v1 v2; refine (@rect2 _ _ _ _ _); simpl; intros.
  + reflexivity.
  + f_equal. apply (H0 Fin.F1 Fin.F1 eq_refl).
    apply H. intros p1 p2 H1;
    apply (H0 (Fin.FS p1) (Fin.FS p2) (f_equal (@Fin.FS n) H1)).
- intros; now f_equal.
Qed.

Lemma nth_order_last A: forall n (v: t A (S n)) (H: n < S n),
 nth_order v H = last v.
Proof.
unfold nth_order; refine (@rectS _ _ _ _); now simpl.
Qed.

Lemma shiftin_nth A a n (v: t A n) k1 k2 (eq: k1 = k2):
  nth (shiftin a v) (Fin.L_R 1 k1) = nth v k2.
Proof.
subst k2; induction k1.
- generalize dependent n. apply caseS ; intros. now simpl.
- generalize dependent n. refine (@caseS _ _ _) ; intros. now simpl.
Qed.

Lemma shiftin_last A a n (v: t A n): last (shiftin a v) = a.
Proof.
induction v ;now simpl.
Qed.

Lemma shiftrepeat_nth A: forall n k (v: t A (S n)),
  nth (shiftrepeat v) (Fin.L_R 1 k) = nth v k.
Proof.
refine (@Fin.rectS _ _ _); lazy beta; [ intros n v | intros n p H v ].
- revert n v; refine (@caseS _ _ _); simpl; intros. now destruct t.
- revert p H.
  refine (match v as v' in t _ m return match m as m' return t A m' -> Prop with
    |S (S n) => fun v => forall p : Fin.t (S n),
      (forall v0 : t A (S n), (shiftrepeat v0) [@ Fin.L_R 1 p ] = v0 [@p]) ->
      (shiftrepeat v) [@Fin.L_R 1 (Fin.FS p)] = v [@Fin.FS p]
    |_ => fun _ => True end v' with
  |[] => I |h :: t => _ end). destruct n0. exact I. now simpl.
Qed.

Lemma shiftrepeat_last A: forall n (v: t A (S n)), last (shiftrepeat v) = last v.
Proof.
refine (@rectS _ _ _ _); now simpl.
Qed.

Lemma const_nth A (a: A) n (p: Fin.t n): (const a n)[@ p] = a.
Proof.
now induction p.
Qed.

Lemma nth_map {A B} (f: A -> B) {n} v (p1 p2: Fin.t n) (eq: p1 = p2):
  (map f v) [@ p1] = f (v [@ p2]).
Proof.
subst p2; induction p1.
- revert n v; refine (@caseS _ _ _); now simpl.
- revert n v p1 IHp1; refine (@caseS _  _ _); now simpl.
Qed.

Lemma nth_map2 {A B C} (f: A -> B -> C) {n} v w (p1 p2 p3: Fin.t n):
  p1 = p2 -> p2 = p3 -> (map2 f v w) [@p1] = f (v[@p2]) (w[@p3]).
Proof.
intros; subst p2; subst p3; revert n v w p1.
refine (@rect2 _ _ _ _ _); simpl.
- exact (Fin.case0 _).
- intros n v1 v2 H a b p; revert n p v1 v2 H; refine (@Fin.caseS _ _ _);
    now simpl.
Qed.

Lemma fold_left_right_assoc_eq {A B} {f: A -> B -> A}
  (assoc: forall a b c, f (f a b) c = f (f a c) b)
  {n} (v: t B n): forall a, fold_left f a v = fold_right (fun x y => f y x) v a.
Proof.
assert (forall n h (v: t B n) a, fold_left f (f a h) v = f (fold_left f a v) h).
- induction v0.
  + now simpl.
  + intros; simpl. rewrite<- IHv0, assoc. now f_equal.
- induction v.
  + reflexivity.
  + simpl. intros; now rewrite<- (IHv).
Qed.

Lemma to_list_of_list_opp {A} (l: list A): to_list (of_list l) = l.
Proof.
induction l.
- reflexivity.
- unfold to_list; simpl. now f_equal.
Qed.

Lemma take_O : forall {A} {n} le (v:t A n), take 0 le v = [].
Proof. 
  reflexivity.
Qed. 

Lemma take_idem : forall {A} p n (v:t A n)  le le', 
  take p le' (take p le v) = take p le v.
Proof. 
  induction p; intros n v le le'.
  - auto. 
  - destruct v. inversion le. simpl. apply f_equal. apply IHp. 
Qed.

Lemma take_app : forall {A} {n} (v:t A n) {m} (w:t A m) le, take n le (append v w) = v.
Proof. 
  induction v; intros m w le.
  - reflexivity. 
  - simpl. apply f_equal. apply IHv. 
Qed.

(* Proof is irrelevant for [take] *)
Lemma take_prf_irr : forall {A} p {n} (v:t A n) le le', take p le v = take p le' v.
Proof. 
  induction p; intros n v le le'. 
  - reflexivity.  
  - destruct v. inversion le. simpl. apply f_equal. apply IHp. 
Qed.

