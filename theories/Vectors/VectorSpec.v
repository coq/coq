(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** N.B.: Using this encoding of vectors is discouraged.
See <https://github.com/coq/coq/blob/master/theories/Vectors/Vector.v>. *)
Attributes warn(cats="stdlib vector", note="Using Vector.t is known to be technically difficult, see <https://github.com/coq/coq/blob/master/theories/Vectors/Vector.v>.").

(** Proofs of specification for functions defined over Vector

   Initial Author: Pierre Boutillier
   Institution: PPS, INRIA 12/2010
*)

#[local] Set Warnings "-stdlib-vector".
Require Fin List.
Require Import VectorDef PeanoNat Eqdep_dec.
Import VectorNotations EqNotations.

Definition cons_inj {A} {a1 a2} {n} {v1 v2 : t A n}
 (eq : a1 :: v1 = a2 :: v2) : a1 = a2 /\ v1 = v2 :=
   match eq in _ = x return caseS _ (fun a2' _ v2' => fun v1' => a1 = a2' /\ v1' = v2') x v1
   with | eq_refl => conj eq_refl eq_refl
   end.

Lemma nil_spec {A} (v : t A 0) : v = [].
Proof.
apply (fun P E => case0 P E v). reflexivity.
Defined.

Lemma eta {A} {n} (v : t A (S n)) : v = hd v :: tl v.
Proof.
apply (fun P IS => caseS P IS (n := n) v); intros; reflexivity.
Defined.

(** Lemmas are done for functions that use [Fin.t] but thanks to [Peano_dec.le_unique], all
is true for the one that use [lt] *)

(** ** Properties of [nth] and [nth_order] *)

Lemma eq_nth_iff A n (v1 v2: t A n):
  (forall p1 p2, p1 = p2 -> v1 [@ p1 ] = v2 [@ p2 ]) <-> v1 = v2.
Proof.
split.
- revert n v1 v2; refine (@rect2 _ _ _ _ _).
  + reflexivity.
  + intros n ? ? H ? ? H0. f_equal.
    * apply (H0 Fin.F1 Fin.F1 eq_refl).
    * apply H. intros p1 p2 H1;
        apply (H0 (Fin.FS p1) (Fin.FS p2) (f_equal (@Fin.FS n) H1)).
- intros; now f_equal.
Qed.

Lemma nth_order_hd A: forall n (v : t A (S n)) (H : 0 < S n),
  nth_order v H = hd v.
Proof. intros n v H; now rewrite (eta v). Qed.

Lemma nth_order_tl A: forall n k (v : t A (S n)) (H : k < n) (HS : S k < S n),
  nth_order (tl v) H = nth_order v HS.
Proof.
intros n; induction n; intros k v H HS.
- inversion H.
- rewrite (eta v).
  unfold nth_order; simpl.
  now rewrite (Fin.of_nat_ext H (proj2 (Nat.succ_lt_mono _ _) HS)).
Qed.

Lemma nth_order_last A: forall n (v: t A (S n)) (H: n < S n),
  nth_order v H = last v.
Proof.
unfold nth_order; refine (@rectS _ _ _ _); now simpl.
Qed.

Lemma nth_order_ext A: forall n k (v : t A n) (H1 H2 : k < n),
  nth_order v H1 = nth_order v H2.
Proof.
intros n k v H1 H2; unfold nth_order.
now rewrite (Fin.of_nat_ext H1 H2).
Qed.

Lemma nth_append_L A: forall n m (v : t A n) (w : t A m) p,
  (v ++ w) [@ Fin.L m p] = v [@ p].
Proof.
intros n m v w. induction v as [|a n v IH].
- apply Fin.case0.
- intros p. now apply (Fin.caseS' p).
Qed.

Lemma nth_append_R A: forall n m (v : t A n) (w : t A m) p,
  (v ++ w) [@ Fin.R n p] = w [@ p].
Proof.
intros n m v w. now induction v.
Qed.

Lemma In_nth A: forall n (v : t A n) p,
  In (nth v p) v.
Proof.
intros n v. induction v as [|a n v IH].
- apply Fin.case0.
- intros p. apply (Fin.caseS' p).
  + apply In_cons_hd.
  + intros q. apply In_cons_tl, IH.
Qed.

(** ** Properties of [replace] *)

Lemma nth_replace_eq A: forall n p (v : t A n) a,
  nth (replace v p a) p = a.
Proof.
intros n p v a. induction v.
- now apply Fin.case0.
- now apply (Fin.caseS' p).
Qed.

Lemma nth_replace_neq A: forall n p q, p <> q -> forall (v : t A n) a,
  nth (replace v q a) p = nth v p.
Proof.
intros n p q Hpq v a.
induction v as [|b n v IH]; revert Hpq.
- now apply Fin.case0.
- apply (Fin.caseS' p); apply (Fin.caseS' q); [easy..|].
  intros ???. apply IH. contradict Hpq. now f_equal.
Qed.

Lemma nth_order_replace_eq A: forall n k (v : t A n) a (H1 : k < n) (H2 : k < n),
  nth_order (replace v (Fin.of_nat_lt H2) a) H1 = a.
Proof.
intros n k v a H1 H2.
rewrite (Fin.of_nat_ext H2 H1).
apply nth_replace_eq.
Qed.

Lemma nth_order_replace_neq A: forall n k1 k2, k1 <> k2 ->
  forall (v : t A n) a (H1 : k1 < n) (H2 : k2 < n),
  nth_order (replace v (Fin.of_nat_lt H2) a) H1 = nth_order v H1.
Proof.
intros n k1 k2 H v a H1 H2.
unfold nth_order. rewrite nth_replace_neq; [reflexivity|].
intros E. apply H.
apply (f_equal (fun p => proj1_sig (Fin.to_nat p))) in E.
now rewrite !Fin.to_nat_of_nat in E.
Qed.

Lemma replace_id A: forall n p (v : t A n),
  replace v p (nth v p) = v.
Proof.
intros n p; induction p as [|? p IHp]; intros v; rewrite (eta v); simpl; [reflexivity|].
now rewrite IHp.
Qed.

Lemma replace_replace_eq A: forall n p (v : t A n) a b,
  replace (replace v p a) p b = replace v p b.
Proof.
intros n p v a b.
induction p as [|? p IHp]; rewrite (eta v); simpl; [reflexivity|].
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
  refine (@rectS _ _ _ _); simpl; intro n; [| do 3 intro]; intros ? ? IH p1 p2; intro Hneq;
    f_equal; apply IH; intros Heq; apply Hneq; now subst.
Qed.

Lemma replace_append_L A: forall n m (v : t A n) (w : t A m) p a,
  replace (v ++ w) (Fin.L m p) a = (replace v p a) ++ w.
Proof.
intros n m v w p a. induction v as [|b n v IH].
- now apply Fin.case0.
- apply (Fin.caseS' p).
  + reflexivity.
  + intros p'. cbn. apply f_equal, IH.
Qed.

Lemma replace_append_R A: forall n m (v : t A n) (w : t A m) p a,
  replace (v ++ w) (Fin.R n p) a = v ++ (replace w p a).
Proof.
intros n m v w p a. induction v as [|b n v IH].
- reflexivity.
- cbn. apply f_equal, IH.
Qed.

(** ** Properties of [const] *)

Lemma const_nth A (a: A) n (p: Fin.t n): (const a n)[@ p] = a.
Proof.
now induction p.
Qed.

Lemma append_const A (a : A) n m : (const a n) ++ (const a m) = const a (n + m).
Proof.
induction n as [|n IH].
- reflexivity.
- cbn. apply f_equal, IH.
Qed.

(** ** Properties of [map] *)

Lemma map_id A: forall n (v : t A n),
  map (fun x => x) v = v.
Proof.
intros n v; induction v as [|? ? v IHv]; simpl; [ | rewrite IHv ]; auto.
Qed.

Lemma map_map A B C: forall (f:A->B) (g:B->C) n (v : t A n),
  map g (map f v) = map (fun x => g (f x)) v.
Proof.
intros f g n v; induction v as [|? ? v IHv]; simpl; [ | rewrite IHv ]; auto.
Qed.

Lemma map_ext_in A B: forall (f g:A->B) n (v : t A n),
  (forall a, In a v -> f a = g a) -> map f v = map g v.
Proof.
intros f g n v H; induction v as [|? ? v IHv].
- reflexivity.
- cbn. now f_equal; [|apply IHv; intros ??]; apply H; [left|right].
Qed.

Lemma map_ext A B: forall (f g:A->B), (forall a, f a = g a) ->
  forall n (v : t A n), map f v = map g v.
Proof.
intros; apply map_ext_in; auto.
Qed.

Lemma nth_map {A B} (f: A -> B) {n} v (p1 p2: Fin.t n) (eq: p1 = p2):
  (map f v) [@ p1] = f (v [@ p2]).
Proof.
subst p2; induction p1 as [n|n p1 IHp1].
- revert n v; refine (@caseS _ _ _); reflexivity.
- revert n v p1 IHp1; refine (@caseS _  _ _); now simpl.
Qed.

Lemma map_append A B: forall (f:A->B) n m (v: t A n) (w: t A m),
  (map f (v ++ w)) = map f v ++ map f w.
Proof.
intros f n m v w. induction v as [|? ? v IHv].
- reflexivity.
- cbn. apply f_equal, IHv.
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

Lemma map2_ext A B C: forall (f g:A->B->C), (forall a b, f a b = g a b) ->
  forall n (v : t A n) (w : t B n), map2 f v w = map2 g v w.
Proof.
intros f g Hfg n v w.
apply (fun P H1 H2 => rect2 P H1 H2 v w).
- reflexivity.
- cbn. intros ??? IH ??. now rewrite IH, Hfg.
Qed.

(** ** Properties of [fold_left] *)

Lemma fold_left_right_assoc_eq {A B} {f: A -> B -> A}
  (assoc: forall a b c, f (f a b) c = f (f a c) b)
  {n} (v: t B n): forall a, fold_left f a v = fold_right (fun x y => f y x) v a.
Proof.
assert (forall n h (v: t B n) a, fold_left f (f a h) v = f (fold_left f a v) h).
- intros n0 h v0; induction v0 as [|? ? v0 IHv0].
  + now simpl.
  + intros; simpl. rewrite<- IHv0, assoc. now f_equal.
- induction v as [|? ? v IHv].
  + reflexivity.
  + simpl. intros; now rewrite<- (IHv).
Qed.

(** ** Properties of [take] *)

Lemma take_O : forall {A} {n} le (v:t A n), take 0 le v = [].
Proof.
  reflexivity.
Qed.

Lemma take_idem : forall {A} p n (v:t A n) le le',
  take p le' (take p le v) = take p le v.
Proof.
  intros A p; induction p as [|p IHp]; intros n v le le'.
  - reflexivity.
  - destruct v.
    + inversion le.
    + simpl. apply f_equal, IHp.
Qed.

Lemma take_app : forall {A} {n} (v:t A n) {m} (w:t A m) le, take n le (append v w) = v.
Proof.
  intros a n v; induction v as [|? ? v IHv]; intros m w le.
  - reflexivity.
  - simpl. apply f_equal, IHv.
Qed.

(* Proof is irrelevant for [take] *)
Lemma take_prf_irr : forall {A} p {n} (v:t A n) le le', take p le v = take p le' v.
Proof.
  intros A p; induction p as [|p IHp]; intros n v le le'.
  - reflexivity.
  - destruct v.
    + inversion le.
    + simpl. apply f_equal, IHp.
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
Proof.
  intros n m v w. induction v as [|a n v IH].
  - reflexivity.
  - cbn. now rewrite IH.
Qed.

Lemma append_splitat {A} : forall {n m : nat} (v : t A n) (w : t A m) (vw : t A (n+m)),
  splitat n vw = (v, w) -> vw = v ++ w.
Proof.
intros n m v w vw E.
assert (v = fst (splitat n vw)) as -> by now rewrite E.
assert (w = snd (splitat n vw)) as -> by now rewrite E.
clear E. induction n as [|n IH].
- reflexivity.
- cbn.
  rewrite (eta vw) at 1.
  rewrite (IH (tl vw)) at 1.
  (* unification keeps unfolding [Nat.add]. In order to destruct
     [splitat n (tl vw)] we need to make all appearances uniform. *)
  change (splitat n (tl vw)) with (splitat n (tl vw)).
  destruct (splitat n (tl vw)) as [??]. reflexivity.
Qed.

Lemma append_inj {A} : forall {n m : nat} (v v' : t A n) (w w' : t A m),
  v ++ w = v' ++ w' -> v = v' /\ w = w'.
Proof.
intros n m v v' w w' E%(f_equal (splitat _)).
apply pair_equal_spec.
now rewrite <- !splitat_append.
Qed.

(** ** Properties of [In] *)

Lemma In_cons_iff A: forall n a b (v : t A n),
  In a (b :: v) <-> (b = a \/ In a v).
Proof.
intros n a b v. split.
- enough (H : forall n (v : t A n), In a v ->
    match v with
    | nil _ => False
    | cons _ b _ v => b = a \/ In a v
    end) by apply H.
  now intros ?? []; [left|right].
- intros [<-|?].
  + apply In_cons_hd.
  + now apply In_cons_tl.
Qed.

(** ** Properties of [Forall] and [Forall2] *)

Lemma Forall_impl A: forall (P Q : A -> Prop), (forall a, P a -> Q a) ->
  forall n (v : t A n), Forall P v -> Forall Q v.
Proof.
intros P Q H n v HPv. now induction HPv; constructor; [apply H|].
Qed.

Lemma Forall_forall A: forall P n (v : t A n),
  Forall P v <-> forall a, In a v -> P a.
Proof.
intros P n v. split.
- intros H. induction H.
  + easy.
  + intros a [<-|?]%In_cons_iff; auto.
- induction v as [|? ? v IHv]; intros Hin; constructor.
  + apply Hin; constructor.
  + apply IHv; intros a Ha.
    apply Hin; now constructor.
Qed.

Lemma Forall_cons_iff A: forall (P : A -> Prop) a n (v : t A n),
  Forall P (a :: v) <-> P a /\ Forall P v.
Proof.
intros P a n v. split.
- rewrite !Forall_forall. intros H. split.
  + apply H, In_cons_hd.
  + intros b Hb. apply H, In_cons_tl, Hb.
- intros [??]. now constructor.
Qed.

Lemma Forall_map A B: forall (P : B -> Prop) (f : A -> B) n (v : t A n),
  Forall P (map f v) <-> Forall (fun x => P (f x)) v.
Proof.
intros P f n v. induction v as [|a n v IH].
- split; constructor.
- cbn. now rewrite !Forall_cons_iff, IH.
Qed.

Lemma Forall_append A: forall P n m (v : t A n) (w : t A m),
  Forall P v -> Forall P w -> Forall P (append v w).
Proof.
intros ????? H ?. induction H.
- easy.
- now constructor.
Qed.

Lemma Forall_nth A: forall P n (v : t A n),
  Forall P v <-> forall p, P (nth v p).
Proof.
intros P n v. split.
- intros H. induction H.
  + apply Fin.case0.
  + intros p. now apply (Fin.caseS' p).
- induction v as [|a v n IH].
  + intros ?. constructor.
  + intros H. constructor.
    * apply (H Fin.F1).
    * apply IH. intros p. apply (H (Fin.FS p)).
Qed.

Lemma Forall_nth_order A: forall P n (v : t A n),
  Forall P v <-> forall i (Hi : i < n), P (nth_order v Hi).
Proof.
intros P n v. rewrite Forall_nth. split.
- intros H i Hi. apply H.
- intros H p.
  rewrite <- (Fin.of_nat_to_nat_inv p).
  apply H.
Qed.

Lemma Forall2_cons_iff A B: forall P n h1 h2 (v1 : t A n) (v2 : t B n),
  Forall2 P (h1 :: v1) (h2 :: v2) <-> P h1 h2 /\ Forall2 P v1 v2.
Proof.
  intros P n h1 h2 v1 v2; split.
  2: { intros [H1 H2]; right; [exact H1 | exact H2]. }
  intros H; inversion H as [| m x1 x2 v0 v3 ph f2p mn [x1h1 H1] [x2h2 H2]].
  split; [exact ph |].
  apply inj_pair2_eq_dec in H1 as ->; [| exact Nat.eq_dec].
  apply inj_pair2_eq_dec in H2 as ->; [| exact Nat.eq_dec].
  exact f2p.
Qed.

Lemma Forall2_nth A: forall P n (v1 v2 : t A n),
  Forall2 P v1 v2 <-> forall p, P (nth v1 p) (nth v2 p).
Proof.
intros P n v1 v2. split.
- intros H. induction H.
  + apply Fin.case0.
  + intros p. now apply (Fin.caseS' p).
- apply (fun P H1 H2 => rect2 P H1 H2 v1 v2).
  + constructor.
  + intros ??? IH ?? H. constructor.
    * apply (H Fin.F1).
    * apply IH. intros p. apply (H (Fin.FS p)).
Qed.

Lemma Forall2_nth_order A: forall P n (v1 v2 : t A n),
     Forall2 P v1 v2
 <-> forall i (Hi1 : i < n) (Hi2 : i < n), P (nth_order v1 Hi1) (nth_order v2 Hi2).
Proof.
intros P n v1 v2. rewrite Forall2_nth. split.
- intros H i Hi1 Hi2.
  rewrite (nth_order_ext _ _ _ _ Hi1 Hi2).
  apply H.
- intros H p.
  rewrite <- (Fin.of_nat_to_nat_inv p).
  apply H.
Qed.

Lemma Forall2_append A B: forall P n m (v : t A n) (v' : t B n) (w : t A m) (w' : t B m),
  Forall2 P v v' -> Forall2 P w w' -> Forall2 P (append v w) (append v' w').
Proof.
intros ??????? H ?. induction H.
- easy.
- now constructor.
Qed.

(** ** Properties of [shiftin] and [shiftrepeat] *)

Lemma shiftin_nth A a n (v: t A n) k1 k2 (eq: k1 = k2):
  nth (shiftin a v) (Fin.L_R 1 k1) = nth v k2.
Proof.
subst k2; induction k1 as [n|n k1 IH].
- revert n v. now apply caseS.
- revert k1 IH. apply (fun P IS => caseS P IS v). now simpl.
Qed.

Lemma shiftin_last A a n (v: t A n): last (shiftin a v) = a.
Proof.
induction v; now simpl.
Qed.

Lemma shiftrepeat_nth A: forall n k (v: t A (S n)),
  nth (shiftrepeat v) (Fin.L_R 1 k) = nth v k.
Proof.
intros n k.
apply (fun P P0 PS => Fin.rectS P P0 PS k); clear n k.
- intros [|n] v; rewrite (eta v); [|reflexivity].
  now rewrite (nil_spec (tl v)).
- intros n k IH v. rewrite (eta v). apply IH.
Qed.

Lemma shiftrepeat_last A: forall n (v: t A (S n)), last (shiftrepeat v) = last v.
Proof.
refine (@rectS _ _ _ _); now simpl.
Qed.

Lemma map_shiftin A B: forall (f : A -> B) a n (v : t A n),
  map f (shiftin a v) = shiftin (f a) (map f v).
Proof.
intros f a n v. induction v as [|b n v IH].
- reflexivity.
- cbn. apply f_equal, IH.
Qed.

Lemma fold_right_shiftin A B: forall (f : A -> B -> B) a b n (v : t A n),
  fold_right f (shiftin b v) a = fold_right f v (f b a).
Proof.
intros f a b n v. induction v as [|c n v IH].
- reflexivity.
- cbn. apply f_equal, IH.
Qed.

Lemma In_shiftin A: forall a b n (v : t A n),
  In a (shiftin b v) <-> (b = a \/ In a v).
Proof.
intros a b n v. induction v as [|c n v IH].
- apply In_cons_iff.
- cbn. rewrite !In_cons_iff. tauto.
Qed.

Lemma Forall_shiftin A: forall (P : A -> Prop) a n (v : t A n),
  Forall P (shiftin a v) <-> (P a /\ Forall P v).
Proof.
intros P a n v. induction v as [|b n v IH].
- apply Forall_cons_iff.
- cbn. rewrite !Forall_cons_iff. tauto.
Qed.

(** ** Properties of [rev] *)

Lemma rev_nil A: rev (nil A) = [].
Proof.
unfold rev, rev_append.
now rewrite (UIP_refl_nat _ (plus_n_O 0)), (UIP_refl_nat _ (Nat.tail_add_spec 0 0)).
Qed.

Lemma rev_cons A: forall a n (v : t A n), rev (a :: v) = shiftin a (rev v).
Proof.
intros a n v. unfold rev, rev_append, eq_rect_r.
rewrite !rew_compose.
enough (H : forall m (w : t A m) k (E1 : _ = k) E2,
  rew [t A] E2 in rev_append_tail v (shiftin a w) =
  shiftin a (rew [t A] E1 in rev_append_tail v w)) by apply (H 0 []).
induction v as [|b n v IH]; intros m w k E1 E2; cbn.
- subst k. now rewrite (UIP_refl_nat _ E2).
- apply (IH _ (b :: w)).
Qed.

Lemma rev_shiftin A: forall a n (v : t A n),
  rev (shiftin a v) = a :: rev v.
Proof.
intros a n v. induction v as [|b n v IH]; cbn.
- now rewrite rev_cons, !rev_nil.
- now rewrite !rev_cons, IH.
Qed.

Lemma rev_rev A: forall n (v : t A n), rev (rev v) = v.
Proof.
intros n v. induction v as [|a n v IH].
- now rewrite !rev_nil.
- now rewrite rev_cons, rev_shiftin, IH.
Qed.

Lemma map_rev A B: forall (f : A -> B) n (v : t A n),
  map f (rev v) = rev (map f v).
Proof.
intros f n v. induction v as [|a n v IH]; cbn.
- now rewrite !rev_nil.
- now rewrite !rev_cons, map_shiftin, IH.
Qed.

Lemma fold_left_rev_right A B: forall (f:A->B->B) n (v : t A n) a,
  fold_right f (rev v) a = fold_left (fun x y => f y x) a v.
Proof.
intros f n v. induction v as [|b n v IH]; intros a.
- now rewrite rev_nil.
- rewrite rev_cons, fold_right_shiftin. apply IH.
Qed.

Lemma In_rev A: forall a n (v : t A n),
  In a (rev v) <-> In a v.
Proof.
intros a n v. induction v as [|b n v IH].
- now rewrite rev_nil.
- now rewrite rev_cons, In_shiftin, In_cons_iff, IH.
Qed.

Lemma Forall_rev A: forall (P : A -> Prop) n (v : t A n),
  Forall P (rev v) <-> Forall P v.
Proof.
intros P n v. induction v as [|a n v IH].
- now rewrite rev_nil.
- now rewrite rev_cons, Forall_shiftin, Forall_cons_iff, IH.
Qed.

(** ** Properties of [to_list] *)

Lemma to_list_of_list_opp {A} (l: list A): to_list (of_list l) = l.
Proof.
induction l.
- reflexivity.
- unfold to_list; simpl. now f_equal.
Qed.

Lemma length_to_list A n (v : t A n): length (to_list v) = n.
Proof. induction v; cbn; auto. Qed.

Lemma of_list_to_list_opp A n (v: t A n):
  rew length_to_list _ _ _ in of_list (to_list v) = v.
Proof.
induction v as [ | h n v IHv ].
- now apply case0 with (P := fun v => v = nil A).
- replace (length_to_list _ _ (cons _ h _ v)) with (f_equal S (length_to_list _ _ v))
    by apply (UIP_dec Nat.eq_dec).
  cbn; rewrite map_subst_map.
  f_equal.
  now etransitivity; [ | apply IHv].
Qed.

Lemma to_list_nil A : to_list (nil A) = List.nil.
Proof. reflexivity. Qed.

Lemma to_list_cons A h n (v : t A n):
  to_list (cons A h n v) = List.cons h (to_list v).
Proof. reflexivity. Qed.

Lemma to_list_nil_iff A v:
  to_list v = List.nil <-> v = nil A.
Proof.
split; intro H.
- now apply case0 with (P := fun v => v = []).
- subst. apply to_list_nil.
Qed.

Lemma to_list_inj A n (v w : t A n):
  to_list v = to_list w -> v = w.
Proof.
revert v. induction w as [| w0 n w IHw].
- apply to_list_nil_iff.
- intros v H. rewrite (eta v) in H.
  injection H as [=H0 H1%IHw]. subst. apply eta.
Qed.

Lemma to_list_hd A n (v : t A (S n)) d:
  hd v = List.hd d (to_list v).
Proof. now rewrite (eta v). Qed.

Lemma to_list_last A n (v : t A (S n)) d:
  last v = List.last (to_list v) d.
Proof.
apply rectS with (v:=v); [reflexivity|].
intros a k u IH.
rewrite to_list_cons.
simpl List.last.
now rewrite <- IH, (eta u).
Qed.

Lemma to_list_const A (a : A) n:
  to_list (const a n) = List.repeat a n.
Proof.
induction n as [ | n IHn ]; [reflexivity|].
now cbn; rewrite <- IHn.
Qed.

Lemma to_list_nth_order A n (v : t A n) p (H : p < n) d:
  nth_order v H = List.nth p (to_list v) d.
Proof.
unfold nth_order. revert p H.
induction v as [|a n v IH].
- intros p H. destruct (Nat.nlt_0_r p H).
- intros [|p] ?; [ reflexivity | apply IH ].
Qed.

Lemma to_list_tl A n (v : t A (S n)):
  to_list (tl v) = List.tl (to_list v).
Proof. now rewrite (eta v). Qed.

Lemma to_list_append A n m (v1 : t A n) (v2 : t A m):
  to_list (append v1 v2) = List.app (to_list v1) (to_list v2).
Proof.
induction v1; simpl; trivial.
now rewrite to_list_cons; f_equal.
Qed.

Lemma to_list_rev_append_tail A n m (v1 : t A n) (v2 : t A m):
  to_list (rev_append_tail v1 v2) = List.rev_append (to_list v1) (to_list v2).
Proof. now revert m v2; induction v1 as [ | ? ? ? IHv1 ]; intros; [ | simpl; rewrite IHv1 ]. Qed.

Lemma to_list_rev_append A n m (v1 : t A n) (v2 : t A m):
  to_list (rev_append v1 v2) = List.rev_append (to_list v1) (to_list v2).
Proof. unfold rev_append; rewrite <- (Nat.tail_add_spec n m); apply to_list_rev_append_tail. Qed.

Lemma to_list_rev A n (v : t A n):
  to_list (rev v) = List.rev (to_list v).
Proof.
unfold rev; rewrite (plus_n_O n); unfold eq_rect_r; simpl.
now rewrite to_list_rev_append, List.rev_alt.
Qed.

Lemma to_list_map A B (f : A -> B) n (v : t A n) :
  to_list (map f v) = List.map f (to_list v).
Proof.
induction v; cbn; [reflexivity|].
now cbn; f_equal.
Qed.

Lemma to_list_fold_left A B f (b : B) n (v : t A n):
  fold_left f b v = List.fold_left f (to_list v) b.
Proof. now revert b; induction v; cbn. Qed.

Lemma to_list_fold_right A B f (b : B) n (v : t A n):
  fold_right f v b = List.fold_right f b (to_list v).
Proof. now revert b; induction v; cbn; intros; f_equal. Qed.

Lemma to_list_Forall A P n (v : t A n):
  Forall P v <-> List.Forall P (to_list v).
Proof.
split; intros HF.
- induction HF; now constructor.
- remember (to_list v) as l.
  revert n v Heql; induction HF; intros n v Heql;
    destruct v; inversion Heql; subst; constructor; auto.
Qed.

Lemma to_list_Exists A P n (v : t A n):
  Exists P v <-> List.Exists P (to_list v).
Proof.
split; intros HF.
- induction HF; now constructor.
- remember (to_list v) as l.
  revert n v Heql; induction HF; intros n v Heql;
    destruct v; inversion Heql; subst; now constructor; auto.
Qed.

Lemma to_list_In A a n (v : t A n):
  In a v <-> List.In a (to_list v).
Proof.
split.
- intros HIn; induction HIn; now constructor.
- induction v; intros HIn; inversion HIn; subst; constructor; auto.
Qed.

Lemma to_list_Forall2 A B P n (v1 : t A n) (v2 : t B n) :
  Forall2 P v1 v2 <-> List.Forall2 P (to_list v1) (to_list v2).
Proof.
split; intros HF.
- induction HF; now constructor.
- remember (to_list v1) as l1.
  remember (to_list v2) as l2.
  revert n v1 v2 Heql1 Heql2; induction HF; intros n v1 v2 Heql1 Heql2.
  + destruct v1; [ | inversion Heql1 ].
    apply case0; constructor.
  + destruct v1; inversion Heql1; subst.
    rewrite (eta v2) in Heql2; inversion Heql2; subst.
    rewrite (eta v2); constructor; auto.
Qed.
