(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

Require Import ZArith.
Require Import BigNumPrelude.
Require Import Max.
Require Import DoubleType.
Require Import DoubleBase.
Require Import CyclicAxioms.
Require Import DoubleCyclic.

Implicit Arguments mk_zn2z_ops [t].
Implicit Arguments mk_zn2z_ops_karatsuba [t].
Implicit Arguments mk_zn2z_specs [t ops].
Implicit Arguments mk_zn2z_specs_karatsuba [t ops].
Implicit Arguments ZnZ.digits [t].
Implicit Arguments ZnZ.zdigits [t].

(* To compute the necessary height *)

Fixpoint plength (p: positive) : positive :=
  match p with
    xH => xH
  | xO p1 => Psucc (plength p1)
  | xI p1 => Psucc (plength p1)
  end.

Theorem plength_correct: forall p, (Zpos p < 2 ^ Zpos (plength p))%Z.
assert (F: (forall p, 2 ^ (Zpos (Psucc p)) = 2 * 2 ^ Zpos p)%Z).
intros p; replace (Zpos (Psucc p)) with (1 + Zpos p)%Z.
rewrite Zpower_exp; auto with zarith.
rewrite Zpos_succ_morphism; unfold Zsucc; auto with zarith.
intros p; elim p; simpl plength; auto.
intros p1 Hp1; rewrite F; repeat rewrite Zpos_xI.
assert (tmp: (forall p, 2 * p = p + p)%Z);
  try repeat rewrite tmp; auto with zarith.
intros p1 Hp1; rewrite F; rewrite (Zpos_xO p1).
assert (tmp: (forall p, 2 * p = p + p)%Z);
  try repeat rewrite tmp; auto with zarith.
rewrite Zpower_1_r; auto with zarith.
Qed.

Theorem plength_pred_correct: forall p, (Zpos p <= 2 ^ Zpos (plength (Ppred p)))%Z.
intros p; case (Psucc_pred p); intros H1.
subst; simpl plength.
rewrite Zpower_1_r; auto with zarith.
pattern p at 1; rewrite <- H1.
rewrite Zpos_succ_morphism; unfold Zsucc; auto with zarith.
generalize (plength_correct (Ppred p)); auto with zarith.
Qed.

Definition Pdiv p q :=
  match Zdiv (Zpos p) (Zpos q) with
    Zpos q1 => match (Zpos p) - (Zpos q) * (Zpos q1) with
                 Z0 => q1
               | _ => (Psucc q1)
               end
  |  _ => xH
  end.

Theorem Pdiv_le: forall p q,
  Zpos p <= Zpos q * Zpos (Pdiv p q).
intros p q.
unfold Pdiv.
assert (H1: Zpos q > 0); auto with zarith.
assert (H1b: Zpos p >= 0); auto with zarith.
generalize (Z_div_ge0 (Zpos p) (Zpos q) H1 H1b).
generalize (Z_div_mod_eq (Zpos p) (Zpos q) H1); case Zdiv.
  intros HH _; rewrite HH; rewrite Zmult_0_r; rewrite Zmult_1_r; simpl.
case (Z_mod_lt (Zpos p) (Zpos q) H1); auto with zarith.
intros q1 H2.
replace (Zpos p - Zpos q * Zpos q1) with (Zpos p mod Zpos q).
  2: pattern (Zpos p) at 2; rewrite H2; auto with zarith.
generalize H2 (Z_mod_lt (Zpos p) (Zpos q) H1); clear H2;
  case Zmod.
  intros HH _; rewrite HH; auto with zarith.
  intros r1 HH (_,HH1); rewrite HH; rewrite Zpos_succ_morphism.
  unfold Zsucc; rewrite Zmult_plus_distr_r; auto with zarith.
  intros r1 _ (HH,_); case HH; auto.
intros q1 HH; rewrite HH.
unfold Zge; simpl Zcompare; intros HH1; case HH1; auto.
Qed.

Definition is_one p := match p with xH => true | _ => false end.

Theorem is_one_one: forall p, is_one p = true -> p = xH.
intros p; case p; auto; intros p1 H1; discriminate H1.
Qed.

Definition get_height digits p :=
  let r := Pdiv p digits in
   if is_one r then xH else Psucc (plength (Ppred r)).

Theorem get_height_correct:
  forall digits N,
   Zpos N <= Zpos digits * (2 ^ (Zpos (get_height digits N) -1)).
intros digits N.
unfold get_height.
assert (H1 := Pdiv_le N digits).
case_eq (is_one (Pdiv N digits)); intros H2.
rewrite (is_one_one _ H2) in H1.
rewrite Zmult_1_r in H1.
change (2^(1-1))%Z with 1; rewrite Zmult_1_r; auto.
clear H2.
apply Zle_trans with (1 := H1).
apply Zmult_le_compat_l; auto with zarith.
rewrite Zpos_succ_morphism; unfold Zsucc.
rewrite Zplus_comm; rewrite Zminus_plus.
apply plength_pred_correct.
Qed.

Definition zn2z_word_comm : forall w n, zn2z (word w n) = word (zn2z w) n.
 fix zn2z_word_comm 2.
 intros w n; case n.
  reflexivity.
  intros n0;simpl.
  case (zn2z_word_comm w n0).
  reflexivity.
Defined.

Fixpoint extend (n:nat) {struct n} : forall w:Type, zn2z w -> word w (S n) :=
 match n return forall w:Type, zn2z w -> word w (S n) with
 | O => fun w x => x
 | S m =>
   let aux := extend m in
   fun w x => WW W0 (aux w x)
 end.

Section ExtendMax.

Open Scope nat_scope.

Fixpoint plusnS (n m: nat) {struct n} : (n + S m = S (n + m))%nat :=
  match n return  (n + S m = S (n + m))%nat with
  | 0 => refl_equal (S m)
  | S n1 =>
      let v := S (S n1 + m) in
      eq_ind_r (fun n => S n = v) (refl_equal v) (plusnS n1 m)
  end.

Fixpoint plusn0 n : n + 0 = n :=
  match n return (n + 0 = n) with
  | 0 => refl_equal 0
  | S n1 =>
      let v := S n1 in
      eq_ind_r (fun n : nat => S n = v) (refl_equal v) (plusn0 n1)
  end.

 Fixpoint diff (m n: nat) {struct m}: nat * nat :=
   match m, n with
     O, n => (O, n)
   | m, O => (m, O)
   | S m1, S n1 => diff m1 n1
   end.

Fixpoint diff_l (m n : nat) {struct m} : fst (diff m n) + n = max m n :=
  match m return fst (diff m n) + n = max m n with
  | 0 =>
      match n return (n = max 0 n) with
      | 0 => refl_equal _
      | S n0 => refl_equal _
      end
  | S m1 =>
      match n return (fst (diff (S m1) n) + n = max (S m1) n)
      with
      | 0 => plusn0 _
      | S n1 =>
          let v := fst (diff m1 n1) + n1 in
          let v1 := fst (diff m1 n1) + S n1 in
          eq_ind v (fun n => v1 = S n)
            (eq_ind v1 (fun n => v1 = n) (refl_equal v1) (S v) (plusnS _ _))
            _ (diff_l _ _)
      end
  end.

Fixpoint diff_r (m n: nat) {struct m}: snd (diff m n) + m = max m n :=
  match m return (snd (diff m n) + m = max m n) with
  | 0 =>
      match n return (snd (diff 0 n) + 0 = max 0 n) with
      | 0 => refl_equal _
      | S _ => plusn0 _
      end
  | S m =>
      match n return (snd (diff (S m) n) + S m = max (S m) n) with
      | 0 => refl_equal (snd (diff (S m) 0) + S m)
      | S n1 =>
          let v := S (max m n1) in
          eq_ind_r (fun n => n = v)
            (eq_ind_r (fun n => S n = v)
               (refl_equal v) (diff_r _ _)) (plusnS _ _)
      end
  end.

 Variable w: Type.

 Definition castm (m n: nat) (H: m = n) (x: word w (S m)):
     (word w (S n)) :=
 match H in (_ = y) return (word w (S y)) with
 | refl_equal => x
 end.

Variable m: nat.
Variable v: (word w (S m)).

Fixpoint extend_tr (n : nat) {struct n}: (word w (S (n + m))) :=
  match n  return (word w (S (n + m))) with
  | O => v
  | S n1 => WW W0 (extend_tr n1)
  end.

End ExtendMax.

Implicit Arguments extend_tr[w m].
Implicit Arguments castm[w m n].



Section Reduce.

 Variable w : Type.
 Variable nT : Type.
 Variable N0 : nT.
 Variable eq0 : w -> bool.
 Variable reduce_n : w -> nT.
 Variable zn2z_to_Nt : zn2z w -> nT.

 Definition reduce_n1 (x:zn2z w) :=
  match x with
  | W0 => N0
  | WW xh xl =>
    if eq0 xh then reduce_n xl
    else zn2z_to_Nt x
  end.

End Reduce.

Section ReduceRec.

 Variable w : Type.
 Variable nT : Type.
 Variable N0 : nT.
 Variable reduce_1n : zn2z w -> nT.
 Variable c : forall n, word w (S n) -> nT.

 Fixpoint reduce_n (n:nat) : word w (S n) -> nT :=
  match n return word w (S n) -> nT with
  | O => reduce_1n
  | S m => fun x =>
    match x with
    | W0 => N0
    | WW xh xl =>
      match xh with
      | W0 => @reduce_n m xl
      | _ => @c (S m) x
      end
    end
  end.

End ReduceRec.

Section CompareRec.

 Variable wm w : Type.
 Variable w_0 : w.
 Variable compare : w -> w -> comparison.
 Variable compare0_m : wm -> comparison.
 Variable compare_m : wm -> w -> comparison.

 Fixpoint compare0_mn (n:nat) : word wm n -> comparison :=
  match n return word wm n -> comparison with
  | O => compare0_m
  | S m => fun x =>
    match x with
    | W0 => Eq
    | WW xh xl =>
      match compare0_mn m xh with
      | Eq => compare0_mn m xl
      | r  => Lt
      end
    end
  end.

 Variable wm_base: positive.
 Variable wm_to_Z: wm -> Z.
 Variable w_to_Z: w -> Z.
 Variable w_to_Z_0: w_to_Z w_0 = 0.
 Variable spec_compare0_m: forall x,
   compare0_m x = (w_to_Z w_0 ?= wm_to_Z x).
 Variable wm_to_Z_pos: forall x, 0 <= wm_to_Z x < base wm_base.

 Let double_to_Z := double_to_Z wm_base wm_to_Z.
 Let double_wB := double_wB wm_base.

 Lemma base_xO: forall n, base (xO n) = (base n)^2.
 Proof.
 intros n1; unfold base.
 rewrite (Zpos_xO n1); rewrite Zmult_comm; rewrite Zpower_mult; auto with zarith.
 Qed.

 Let double_to_Z_pos: forall n x, 0 <= double_to_Z n x < double_wB n :=
   (spec_double_to_Z wm_base wm_to_Z wm_to_Z_pos).


 Lemma spec_compare0_mn: forall n x,
   compare0_mn n x = (0 ?= double_to_Z n x).
 Proof.
  intros n; elim n; clear n; auto.
  intros x; rewrite spec_compare0_m; rewrite w_to_Z_0; auto.
  intros n Hrec x; case x; unfold compare0_mn; fold compare0_mn; auto.
  fold word in *.
  intros xh xl.
  rewrite 2 Hrec.
  simpl double_to_Z.
  set (wB := DoubleBase.double_wB wm_base n).
  case Zcompare_spec; intros Cmp.
  rewrite <- Cmp. reflexivity.
  symmetry. apply Zgt_lt, Zlt_gt. (* ;-) *)
  assert (0 < wB).
   unfold wB, DoubleBase.double_wB, base; auto with zarith.
  change 0 with (0 + 0); apply Zplus_lt_le_compat; auto with zarith.
  apply Zmult_lt_0_compat; auto with zarith.
  case (double_to_Z_pos n xl); auto with zarith.
  case (double_to_Z_pos n xh); intros; exfalso; omega.
  Qed.

 Fixpoint compare_mn_1 (n:nat) : word wm n -> w -> comparison :=
  match n return word wm n -> w -> comparison with
  | O => compare_m
  | S m => fun x y =>
    match x with
    | W0 => compare w_0 y
    | WW xh xl =>
      match compare0_mn m xh with
      | Eq => compare_mn_1 m xl y
      | r  => Gt
      end
    end
  end.

 Variable spec_compare: forall x y,
   compare x y = Zcompare (w_to_Z x) (w_to_Z y).
 Variable spec_compare_m: forall x y,
   compare_m x y = Zcompare (wm_to_Z x) (w_to_Z y).
 Variable wm_base_lt: forall x,
   0 <= w_to_Z x < base (wm_base).

 Let double_wB_lt: forall n x,
   0 <= w_to_Z x < (double_wB n).
 Proof.
 intros n x; elim n; simpl; auto; clear n.
 intros n (H0, H); split; auto.
 apply Zlt_le_trans with (1:= H).
 unfold double_wB, DoubleBase.double_wB; simpl.
 rewrite base_xO.
 set (u := base (double_digits wm_base n)).
 assert (0 < u).
  unfold u, base; auto with zarith.
 replace (u^2) with (u * u); simpl; auto with zarith.
 apply Zle_trans with (1 * u); auto with zarith.
 unfold Zpower_pos; simpl; ring.
 Qed.


 Lemma spec_compare_mn_1: forall n x y,
   compare_mn_1 n x y = Zcompare (double_to_Z n x) (w_to_Z y).
 Proof.
 intros n; elim n; simpl; auto; clear n.
 intros n Hrec x; case x; clear x; auto.
 intros y; rewrite spec_compare; rewrite w_to_Z_0. reflexivity.
 intros xh xl y; simpl;
 rewrite spec_compare0_mn, Hrec. case Zcompare_spec.
 intros H1b.
 rewrite <- H1b; rewrite Zmult_0_l; rewrite Zplus_0_l; auto.
 symmetry. apply Zlt_gt.
 case (double_wB_lt n y); intros _ H0.
 apply Zlt_le_trans with (1:= H0).
 fold double_wB.
 case (double_to_Z_pos n xl); intros H1 H2.
 apply Zle_trans with (double_to_Z n xh * double_wB n); auto with zarith.
 apply Zle_trans with (1 * double_wB n); auto with zarith.
 case (double_to_Z_pos n xh); intros; exfalso; omega.
 Qed.

End CompareRec.


Section AddS.

 Variable w wm : Type.
 Variable incr : wm -> carry wm.
 Variable addr : w -> wm -> carry wm.
 Variable injr : w -> zn2z wm.

 Variable w_0 u: w.
 Fixpoint injs  (n:nat): word w (S n) :=
  match n return (word w (S n)) with
    O => WW w_0 u
  | S n1 => (WW W0 (injs n1))
  end.

 Definition adds x y :=
   match y with
    W0 => C0 (injr x)
  | WW hy ly => match addr x ly with
                  C0 z => C0 (WW hy z)
                | C1 z => match incr hy with
                            C0 z1 => C0 (WW z1 z)
                          | C1 z1 => C1 (WW z1 z)
                          end
                 end
   end.

End AddS.

 Fixpoint length_pos x :=
  match x with xH => O | xO x1 => S (length_pos x1) | xI x1 => S (length_pos x1) end.

 Theorem length_pos_lt: forall x y,
   (length_pos x < length_pos y)%nat -> Zpos x < Zpos y.
 Proof.
 intros x; elim x; clear x; [intros x1 Hrec | intros x1 Hrec | idtac];
   intros y; case y; clear y; intros y1 H || intros H; simpl length_pos;
   try (rewrite (Zpos_xI x1) || rewrite (Zpos_xO x1));
   try (rewrite (Zpos_xI y1) || rewrite (Zpos_xO y1));
   try (inversion H; fail);
   try (assert (Zpos x1 < Zpos y1); [apply Hrec; apply lt_S_n | idtac]; auto with zarith);
   assert (0 < Zpos y1); auto with zarith; red; auto.
 Qed.

 Theorem cancel_app: forall A B (f g: A -> B) x, f = g -> f x = g x.
 Proof.
 intros A B f g x H; rewrite H; auto.
 Qed.


 Section SimplOp.

 Variable w: Type.

 Theorem digits_zop: forall t (ops : ZnZ.Ops t),
  ZnZ.digits (mk_zn2z_ops ops) = xO (ZnZ.digits ops).
 Proof.
 intros ww x; auto.
 Qed.

 Theorem digits_kzop: forall t (ops : ZnZ.Ops t),
  ZnZ.digits (mk_zn2z_ops_karatsuba ops) = xO (ZnZ.digits ops).
 Proof.
 intros ww x; auto.
 Qed.

 Theorem make_zop: forall t (ops : ZnZ.Ops t),
  @ZnZ.to_Z _ (mk_zn2z_ops ops) =
    fun z => match z with
             | W0 => 0
             | WW xh xl => ZnZ.to_Z xh * base (ZnZ.digits ops)
                                + ZnZ.to_Z xl
             end.
 Proof.
 intros ww x; auto.
 Qed.

 Theorem make_kzop: forall t (ops: ZnZ.Ops t),
  @ZnZ.to_Z _ (mk_zn2z_ops_karatsuba ops) =
    fun z => match z with
             | W0 => 0
             | WW xh xl => ZnZ.to_Z xh * base (ZnZ.digits ops)
                                + ZnZ.to_Z xl
             end.
 Proof.
 intros ww x; auto.
 Qed.

 End SimplOp.

(** TODO : to migrate in NArith *)

 Notation Pshiftl := DoubleBase.double_digits.

 Lemma Pshiftl_plus : forall n m p,
  Pshiftl p (m + n) = Pshiftl (Pshiftl p n) m.
 Proof.
 induction m; simpl; congruence.
 Qed.

 Lemma Pshiftl_Zpower : forall n d,
  Zpos (Pshiftl d n) = (Zpos d * 2 ^ Z_of_nat n)%Z.
 Proof.
 intros.
 rewrite Zmult_comm.
 induction n. simpl; auto.
 transitivity (2 * (2 ^ Z_of_nat n * Zpos d))%Z.
 rewrite <- IHn. auto.
 rewrite Zmult_assoc.
 rewrite <- Zpower_Zsucc, inj_S; auto with zarith.
 Qed.

(** END TODO *)

(** Abstract vision of a datatype of arbitrary-large numbers.
    Concrete operations can be derived from these generic
    fonctions, in particular from [iter_t] and [same_level].
*)

Module Type NAbstract.

(** The domains: a sequence of [Z/nZ] structures *)

Parameter dom_t : nat -> Type.
Declare Instance dom_op n : ZnZ.Ops (dom_t n).
Declare Instance dom_spec n : ZnZ.Specs (dom_op n).

Axiom digits_dom_op : forall n,
  ZnZ.digits (dom_op n) = Pshiftl (ZnZ.digits (dom_op 0)) n.

(** The type [t] of arbitrary-large numbers, with abstract constructor [mk_t]
    and destructor [destr_t] and iterator [iter_t] *)

Parameter t : Type.

Parameter mk_t : forall (n:nat), dom_t n -> t.

Inductive View_t : t -> Prop :=
 Mk_t : forall n (x : dom_t n), View_t (mk_t n x).

Axiom destr_t : forall x, View_t x. (* i.e. every x is a (mk_t n xw) *)

Parameter iter_t : forall {A:Type}(f : forall n, dom_t n -> A), t -> A.

Axiom iter_mk_t : forall A (f:forall n, dom_t n -> A),
 forall n x, iter_t f (mk_t n x) = f n x.

(** Conversion to [ZArith] *)

Parameter to_Z : t -> Z.
Local Notation "[ x ]" := (to_Z x).

Axiom spec_mk_t : forall n x, [mk_t n x] = ZnZ.to_Z x.

(** [reduce] is like [mk_t], but try to minimise the level of the number *)

Parameter reduce : forall (n:nat), dom_t n -> t.
Axiom spec_reduce : forall n x, [reduce n x] = ZnZ.to_Z x.

(** Number of level in the tree representation of a number.
    NB: This function isn't a morphism for setoid [eq]. *)

Definition level := iter_t (fun n _ => n).

(** [same_level] and its rich specification, indexed by [level] *)

Parameter same_level : forall {A:Type}
 (f : forall n, dom_t n -> dom_t n -> A), t -> t -> A.

Axiom spec_same_level_dep :
  forall res
   (P : nat -> Z -> Z -> res -> Prop)
   (Pantimon : forall n m z z' r, (n <= m)%nat -> P m z z' r -> P n z z' r)
   (f : forall n, dom_t n -> dom_t n -> res)
   (Pf: forall n x y, P n (ZnZ.to_Z x) (ZnZ.to_Z y) (f n x y)),
   forall x y, P (level y) [x] [y] (same_level f x y).

(** [mk_t_S] : building a number of the next level *)

Parameter mk_t_S : forall (n:nat), zn2z (dom_t n) -> t.

Axiom spec_mk_t_S : forall n (x:zn2z (dom_t n)),
  [mk_t_S n x] = zn2z_to_Z (base (ZnZ.digits (dom_op n))) ZnZ.to_Z x.

Axiom mk_t_S_level : forall n x, level (mk_t_S n x) = S n.

End NAbstract.
