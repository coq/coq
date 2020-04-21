(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
Require Import VectorDef PeanoNat Eqdep_dec.
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

(** ** Properties of [nth] and [nth_order] *)

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

Lemma nth_order_hd A: forall n (v : t A (S n)) (H : 0 < S n),
  nth_order v H = hd v.
Proof. intros; now rewrite (eta v). Qed.

Lemma nth_order_tl A: forall n k (v : t A (S n)) (H : k < n) (HS : S k < S n),
  nth_order (tl v) H = nth_order v HS.
Proof.
induction n; intros.
- inversion H.
- rewrite (eta v).
  unfold nth_order; simpl.
  now rewrite (Fin.of_nat_ext H (Lt.lt_S_n _ _ HS)).
Qed.

Lemma nth_order_last A: forall n (v: t A (S n)) (H: n < S n),
 nth_order v H = last v.
Proof.
unfold nth_order; refine (@rectS _ _ _ _); now simpl.
Qed.

Lemma nth_order_ext A: forall n k (v : t A n) (H1 H2 : k < n),
  nth_order v H1 = nth_order v H2.
Proof.
intros; unfold nth_order.
now rewrite (Fin.of_nat_ext H1 H2).
Qed.

(** ** Properties of [shiftin] and [shiftrepeat] *)

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

(** ** Properties of [replace] *)

Lemma nth_order_replace_eq A: forall n k (v : t A n) a (H1 : k < n) (H2 : k < n),
  nth_order (replace v (Fin.of_nat_lt H2) a) H1 = a.
Proof.
intros n k; revert n; induction k; intros;
  (destruct n; [ inversion H1 | subst ]).
- now rewrite nth_order_hd, (eta v).
- rewrite <- (nth_order_tl _ _ _ _ (proj2 (Nat.succ_lt_mono _ _) H1)), (eta v).
  apply IHk.
Qed.

Lemma nth_order_replace_neq A: forall n k1 k2, k1 <> k2 ->
  forall (v : t A n) a (H1 : k1 < n) (H2 : k2 < n),
  nth_order (replace v (Fin.of_nat_lt H2) a) H1 = nth_order v H1.
Proof.
intros n k1; revert n; induction k1; intros;
  (destruct n ; [ inversion H1 | subst ]).
- rewrite 2 nth_order_hd.
  destruct k2; intuition.
  now rewrite 2 (eta v).
- rewrite <- 2 (nth_order_tl _ _ _ _ (proj2 (Nat.succ_lt_mono _ _) H1)), (eta v).
  destruct k2; auto.
  apply IHk1.
  intros Hk; apply H; now subst.
Qed.

Lemma replace_id A: forall n p (v : t A n),
  replace v p (nth v p) = v.
Proof.
induction p; intros; rewrite 2 (eta v); simpl; auto.
now rewrite IHp.
Qed.

Lemma replace_replace_eq A: forall n p (v : t A n) a b,
  replace (replace v p a) p b = replace v p b.
Proof.
intros.
induction p; rewrite 2 (eta v); simpl; auto.
now rewrite IHp.
Qed.

Lemma replace_replace_neq A: forall n p1 p2 (v : t A n) a b, p1 <> p2 ->
  replace (replace v p1 a) p2 b = replace (replace v p2 b) p1 a.
Proof.
apply (Fin.rect2 (fun n p1 p2 => forall v a b,
  p1 <> p2 -> replace (replace v p1 a) p2 b = replace (replace v p2 b) p1 a)).
- intros n v a b Hneq.
  now contradiction Hneq.
- intros n p2 v; revert n v p2.
  refine (@rectS _ _ _ _); auto.
- intros n p1 v; revert n v p1.
  refine (@rectS _ _ _ _); auto.
- intros n p1 p2 IH v; revert n v p1 p2 IH.
  refine (@rectS _ _ _ _); simpl; do 6 intro; [ | do 3 intro ]; intro Hneq;
    f_equal; apply IH; intros Heq; apply Hneq; now subst.
Qed.

(** ** Properties of [const] *)

Lemma const_nth A (a: A) n (p: Fin.t n): (const a n)[@ p] = a.
Proof.
now induction p.
Qed.

(** ** Properties of [map] *)

Lemma map_id A: forall n (v : t A n),
  map (fun x => x) v = v.
Proof.
induction v; simpl; [ | rewrite IHv ]; auto.
Qed.

Lemma map_map A B C: forall (f:A->B) (g:B->C) n (v : t A n),
  map g (map f v) = map (fun x => g (f x)) v.
Proof.
induction v; simpl; [ | rewrite IHv ]; auto.
Qed.

Lemma map_ext_in A B: forall (f g:A->B) n (v : t A n),
  (forall a, In a v -> f a = g a) -> map f v = map g v.
Proof.
induction v; simpl; auto.
intros; rewrite H by constructor; rewrite IHv; intuition.
apply H; now constructor.
Qed.

Lemma map_ext A B: forall (f g:A->B), (forall a, f a = g a) ->
  forall n (v : t A n), map f v = map g v.
Proof.
intros; apply map_ext_in; auto.
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

(** ** Properties of [fold_left] *)

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

(** ** Properties of [to_list] *)

Lemma to_list_of_list_opp {A} (l: list A): to_list (of_list l) = l.
Proof.
induction l.
- reflexivity.
- unfold to_list; simpl. now f_equal.
Qed.

(** ** Properties of [take] *)

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

(** ** Properties of [uncons] and [splitat] *)

Lemma uncons_cons {A} : forall {n : nat} (a : A) (v : t A n),
    uncons (a::v) = (a,v).
Proof. reflexivity. Qed.

(* [append] *)

Lemma append_comm_cons {A} : forall {n m : nat} (v : t A n) (w : t A m) (a : A),
    a :: (v ++ w) = (a :: v) ++ w.
Proof. reflexivity. Qed.

Lemma splitat_append {A} : forall {n m : nat} (v : t A n) (w : t A m),
    splitat n (v ++ w) = (v, w).
Proof with simpl; auto.
  intros n m v.
  generalize dependent m.
  induction v; intros...
  rewrite IHv...
Qed.

Lemma append_splitat {A} : forall {n m : nat} (v : t A n) (w : t A m) (vw : t A (n+m)),
    splitat n vw = (v, w) ->
    vw = v ++ w.
Proof with auto.
  intros n m v.
  generalize dependent m.
  induction v; intros; inversion H...
  destruct (splitat n (tl vw)) as [v' w'] eqn:Heq.
  apply pair_equal_spec in H1.
  destruct H1; subst.
  rewrite <- append_comm_cons.
  rewrite (eta vw).
  apply cons_inj in H0.
  destruct H0; subst.
  f_equal...
  apply IHv...
Qed.

(** ** Properties of [Forall] and [Forall2] *)

Lemma Forall_impl A: forall (P Q : A -> Prop), (forall a, P a -> Q a) ->
  forall n (v : t A n), Forall P v -> Forall Q v.
Proof.
induction v; intros HP; constructor; inversion HP as [| ? ? ? ? ? Heq1 [Heq2 He]];
  apply (inj_pair2_eq_dec _ Nat.eq_dec) in He; subst; intuition.
Qed.

Lemma Forall_forall A: forall P n (v : t A n),
  Forall P v <-> forall a, In a v -> P a.
Proof.
intros P n v; split.
- intros HP a Hin.
  revert HP; induction Hin; intros HP;
    inversion HP as [| ? ? ? ? ? Heq1 [Heq2 He]]; subst; auto.
  apply (inj_pair2_eq_dec _ Nat.eq_dec) in He; subst; auto.
- induction v; intros Hin; constructor.
  + apply Hin; constructor.
  + apply IHv; intros a Ha.
    apply Hin; now constructor.
Qed.

Lemma Forall_nth_order A: forall P n (v : t A n),
  Forall P v <-> forall i (Hi : i < n), P (nth_order v Hi).
Proof.
split; induction n.
- intros HF i Hi; inversion Hi.
- intros HF i Hi.
  rewrite (eta v).
  rewrite (eta v) in HF.
  inversion HF as [| ? ? ? ? ? Heq1 [Heq2 He]]; subst.
  apply (inj_pair2_eq_dec _ Nat.eq_dec) in He ; subst.
  destruct i.
  + now rewrite nth_order_hd.
  + rewrite <- (nth_order_tl _ _ _ _ (proj2 (Nat.succ_lt_mono _ _) Hi) Hi).
    now apply IHn.
- intros HP; apply case0; constructor.
- intros HP.
  rewrite (eta v) in HP.
  rewrite (eta v); constructor.
  + specialize HP with 0 (Nat.lt_0_succ n).
    now rewrite nth_order_hd in HP.
  + apply IHn; intros.
    specialize HP with (S i) (proj1 (Nat.succ_lt_mono _ _) Hi).
    now rewrite <- (nth_order_tl _ _ _ _ Hi) in HP.
Qed.

Lemma Forall2_nth_order A: forall P n (v1 v2 : t A n),
     Forall2 P v1 v2
 <-> forall i (Hi1 : i < n) (Hi2 : i < n), P (nth_order v1 Hi1) (nth_order v2 Hi2).
Proof.
split; induction n.
- intros HF i Hi1 Hi2; inversion Hi1.
- intros HF i Hi1 Hi2.
  rewrite (eta v1), (eta v2).
  rewrite (eta v1), (eta v2) in HF.
  inversion HF as [| ? ? ? ? ? ? ? Heq [Heq1 He1] [Heq2 He2]].
  apply (inj_pair2_eq_dec _ Nat.eq_dec) in He1.
  apply (inj_pair2_eq_dec _ Nat.eq_dec) in He2; subst.
  destruct i.
  + now rewrite nth_order_hd.
  + rewrite <- (nth_order_tl _ _ _ _ (proj2 (Nat.succ_lt_mono _ _) Hi1) Hi1).
    rewrite <- (nth_order_tl _ _ _ _ (proj2 (Nat.succ_lt_mono _ _) Hi2) Hi2).
    now apply IHn.
- intros _; revert v1; apply case0; revert v2; apply case0; constructor.
- intros HP.
  rewrite (eta v1), (eta v2) in HP.
  rewrite (eta v1), (eta v2); constructor.
  + specialize HP with 0 (Nat.lt_0_succ _) (Nat.lt_0_succ _).
    now rewrite nth_order_hd in HP.
  + apply IHn; intros.
    specialize HP with (S i) (proj1 (Nat.succ_lt_mono _ _) Hi1)
                             (proj1 (Nat.succ_lt_mono _ _) Hi2).
    now rewrite <- (nth_order_tl _ _ _ _ Hi1), <- (nth_order_tl _ _ _ _ Hi2)  in HP.
Qed.
