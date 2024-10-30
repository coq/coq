Require Import List Permutation Morphisms ZArith Lia.
Import ListNotations.

Module Import List.
Notation map_snoc := map_last.

Lemma seq_mul_r s n c :
  seq s (n*c) = concat (map (fun i => seq (s + i*c) c) (seq O n)).
Proof.
  revert s; induction n; intros; rewrite ?flat_map_nil_l, ?Nat.add_0_r; trivial.
  cbn [Nat.mul]; rewrite Nat.add_comm, seq_app.
  rewrite seq_S, map_app, concat_app, IHn; cbn [concat map]; rewrite app_nil_r; trivial.
Qed.

Lemma seq_0_mul n c :
  seq O (n*c) = concat (map (fun i => seq (i*c) c) (seq O n)).
Proof. apply seq_mul_r. Qed.

Lemma map_const {A B} x l : @map A B (fun _ => x) l = repeat x (length l).
Proof. induction l; cbn; congruence. Qed.

Lemma map_add_seq a s l : map (Nat.add a) (seq s l) = seq (a+s) l.
Proof.
  revert s; induction l; intros; cbn [seq map]; rewrite ?IHl, ?Nat.add_succ_r; trivial.
Qed.

Lemma seq_as_seq0 s l : seq s l = map (Nat.add s) (seq 0 l).
Proof. rewrite map_add_seq, Nat.add_0_r; trivial. Qed.

Notation map_concat := concat_map.

Lemma concat_map_map_const_r {A B C} (f : A -> B -> C) l l' :
  concat (map (fun x => map (f x) l) l') = map (uncurry f) (list_prod l' l).
Proof.
  induction l'; cbn [concat map list_prod]; trivial.
  rewrite IHl', map_app, map_map; trivial.
Qed.

Lemma list_prod_nil_r {A B} l : @list_prod A B l [] = [].
Proof. induction l; cbn; auto. Qed.
End List.

Module Import Permutation.
Lemma Permutation_list_prod_cons_r {A B} a (l : list A) (l' : list B) :
  Permutation (list_prod l (a :: l'))
              (map (fun x : A => (x, a)) l ++ list_prod l l').
Proof.
  revert l'; revert a; induction l; cbn; constructor.
  etransitivity. eapply Permutation_app. 2: eapply IHl. reflexivity.
  rewrite !app_assoc. eapply Permutation_app; trivial.
  eapply Permutation_app_comm.
Qed.

Lemma Permutation_flip_list_prod {A B} (l : list A) (l' : list B) :
  Permutation (map (fun p => (snd p, fst p)) (list_prod l' l)) (list_prod l l').
Proof.
  induction l'; cbn; rewrite ?list_prod_nil_r; trivial.
  rewrite map_app, map_map, IHl'; cbn [fst snd].
  eapply symmetry, Permutation_list_prod_cons_r.
Qed.
End Permutation.

Module Import Nat.
  Local Open Scope nat_scope.
  Definition sum := (fold_right Nat.add 0%nat).
  Lemma sum_app l l' : sum (l ++ l') = sum l + sum l'.
  Proof.
    induction l; cbn [app sum fold_right];
      rewrite ?Nat.add_0_l, ?IHl, ?Nat.add_assoc; trivial.
  Qed.
  Lemma sum_snoc l n : sum (l ++ [n]) = sum l + n.
  Proof. rewrite sum_app; cbn [sum fold_right]; rewrite ?Nat.add_0_r; trivial. Qed.
End Nat.

Module Import Z.
  Local Open Scope Z_scope.
  Definition sum := (fold_right Z.add 0).
  Lemma sum_repeat x n : sum (repeat x n) = x * Z.of_nat n.
  Proof. induction n; cbn [sum fold_right repeat]; lia. Qed.

  Lemma sum_repeat_0 n : sum (repeat 0 n) = 0.
  Proof. rewrite sum_repeat; trivial. Qed.

  Lemma sum_app l l' : sum (l ++ l') = sum l + sum l'.
  Proof.
    induction l; cbn [app sum fold_right];
      rewrite ?Z.add_0_l, ?IHl, ?Z.add_assoc; trivial.
  Qed.

  Lemma sum_snoc l z : sum (l ++ [z]) = sum l + z.
  Proof. rewrite sum_app; cbn [sum fold_right]; rewrite ?Z.add_0_r; trivial. Qed.

  Lemma sum_map_mul z l : sum (map (Z.mul z) l) = z * sum l.
  Proof. induction l; cbn [map sum fold_right]; lia. Qed.

  Lemma sum_concat l : sum (concat l) = sum (map Z.sum l).
  Proof. induction l; cbn [map sum fold_right concat]; rewrite ?sum_app; lia. Qed.

  Global Instance Proper_sum_Permutation : Proper (@Permutation Z ==> eq) sum.
  Proof. induction 1; cbn [sum fold_right]; lia. Qed.

  Lemma sum_map_swap_indep {A B} (f : A -> B -> Z) l l' :
    Z.sum (map (fun x => Z.sum (map (fun y => f x y) l)) l') =
    Z.sum (map (fun y => Z.sum (map (fun x => f x y) l')) l).
  Proof.
    erewrite <-map_map, <-sum_concat; symmetry.
    erewrite <-map_map, <-sum_concat; symmetry.
    eapply Proper_sum_Permutation.
    rewrite 2 concat_map_map_const_r.
    rewrite <-Permutation_flip_list_prod.
    erewrite map_map, map_ext; try intros []; trivial.
  Qed.
End Z.

Local Notation "[ e | x <- 'rev' ( s ..+ l ) ]" :=
  (map (fun x : nat => e) (List.rev (seq s%nat l%nat)))
  (format "[  e  '[hv' |  x  <-  'rev' ( s  ..+  l ) ']'  ]", x name).
Local Notation "[ e | x <- s ..+ l ]" :=
  (map (fun x : nat => e) (seq s%nat l%nat))
  (format "[  e  '[hv' |  x  <-  s  ..+  l ']'  ]", x name).
Local Notation "∑ l" := (Z.sum l%Z) (format "∑ l", at level 10) : Z_scope.
Local Notation "∑ l" := (Nat.sum l%nat) (format "∑ l", at level 10) : nat_scope.

Section __. (* https://www.shiftleft.org/papers/fff/fff.pdf section 3.3 *)
Context (n : nat) (s t : nat -> nat) (d : nat -> Z) s_max (Hs_max : forall j, s j <= s_max).
Implicit Types i j k : nat.
Local Coercion Z.of_nat : nat >-> Z.
Definition o j : nat := ∑ [s j * t j | j<-0..+j]. Definition D := o n.
Definition spec : Z := ∑ [ 2^i * d i  | i<-0..+D].
Definition C j k : Z := ∑ [d (o j + s j * i + k) * 2^(o j + s j * i) | i<-0..+t j].
Definition impl :=
  fold_left (fun r t => 2*r +t)%Z
    [ ∑[ if (k <? s j)%nat then C j k else 0 | j<-rev(0..+n) ]
    | k<-rev(0..+s_max) ]%Z 0%Z.
Lemma impl_correct : impl = spec.
Proof.
  cbv [impl]; transitivity (∑[2^k * ∑[if (k <? s j)%nat then C j k else 0
                | j<-rev(0..+n) ] | k<-0..+s_max ])%Z. {
    set (fun k => _) as f; change (fun k => 2^k*_)%Z with (fun k => 2^k*f k)%Z.
    rewrite <-Z.add_0_r; rewrite <-(Z.mul_0_l (2^s_max)) at 2.
    generalize 0%Z as r; clear Hs_max. induction s_max as [|? IH]; intros.
    { symmetry. apply Z.mul_1_r. }
    rewrite seq_S, rev_unit, map_snoc, Z.sum_snoc, Nat.add_0_l; cbn [map fold_left].
    rewrite IH; rewrite <-?Z.add_assoc, ?Nat2Z.inj_succ, ?Z.pow_succ_r; lia. }
  transitivity (∑[∑[if (k <? s j)%nat then 2^k * C j k else 0
                | j<-rev(0..+n) ] | k<-0..+s_max ])%Z.
  { remember(*nodelta*)C; setoid_rewrite <-Z.sum_map_mul; setoid_rewrite map_map.
    setoid_rewrite (_ : forall a b c d,
      (a*(if b:bool then c else d)) = (if b then a*c else a*d))%Z; cycle 1.
    { intros; case b; trivial. } { setoid_rewrite Z.mul_0_r; trivial. } }
  transitivity (∑[∑[ 2^k * C j k | k<-0 ..+s j ] | j<-rev(0..+n) ])%Z. {
    rewrite sum_map_swap_indep. f_equal. f_equiv; intro j.
    rewrite <-(Nat.sub_add (s j) s_max), Nat.add_comm by trivial.
    rewrite seq_app, map_app, Z.sum_app.
    erewrite map_ext_in; cycle 1; try intros k Hk%in_seq.
    { destruct (Nat.ltb_spec k (s j)); try lia. exact eq_refl. }
    erewrite map_ext_in with (f:=fun k=>if _<?_ then _ else _), map_const, sum_repeat_0;
      try (intros k Hk%in_seq; destruct (Nat.ltb_spec k (s j))); lia. }
  transitivity (∑[∑[∑[ d (o j + s j * i + k) * 2 ^ (o j + s j * i + k)
                | k<-0..+s j ] | i<-0..+t j ] | j<-0..+n ])%Z. {
    cbv [C]. setoid_rewrite <-sum_map_mul; setoid_rewrite map_map.
    setoid_rewrite Z.mul_comm at 1.
    setoid_rewrite <-Z.mul_assoc.
    setoid_rewrite <-Z.pow_add_r; try lia.
    setoid_rewrite <-Permutation_rev.
    setoid_rewrite sum_map_swap_indep at 1. trivial. }
  transitivity (∑[∑[ d (o j + k) * 2^(o j + k) | k<-0..+(s j * t j)] | j<-0..+n ])%Z. {
    symmetry; setoid_rewrite Nat.mul_comm at 1; setoid_rewrite seq_0_mul.
      setoid_rewrite map_concat; setoid_rewrite map_map.
      setoid_rewrite sum_concat; setoid_rewrite map_map.
    setoid_rewrite (seq_as_seq0 (_ * _)).
      setoid_rewrite Nat.mul_comm at 1. setoid_rewrite map_map.
    setoid_rewrite Nat2Z.inj_add; setoid_rewrite Nat2Z.inj_mul.
    setoid_rewrite Z.add_assoc; setoid_rewrite Nat.add_assoc. trivial. }
  cbv [spec]; assert (seq 0 D = concat [ seq (o x) (s x * t x) | x<-0..+n ]) as ->. {
    cbv [D o]; induction n as [|? IH]; trivial.
    rewrite ?seq_S, ?map_snoc, ?concat_app; cbn [concat]; rewrite ?app_nil_r, <-IH.
    rewrite Nat.sum_snoc, (seq_app (Nat.sum _)); trivial. }
  setoid_rewrite concat_map; setoid_rewrite map_map. setoid_rewrite (Z.mul_comm (_^_)).
  setoid_rewrite seq_as_seq0 at 3; setoid_rewrite map_map.
  rewrite sum_concat, map_map. setoid_rewrite Nat2Z.inj_add. trivial.
Qed.
End __.
