(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(** This file includes random facts about Integers (and natural numbers) which are not found in the standard library. Some of the lemma here are not used in the QArith developement but are rather useful.
*)

Require Export ZArith.
Require Export ZArithRing.

Tactic Notation "ElimCompare" constr(c) constr(d) := elim_compare c d.

Ltac Flip :=
  apply Z.gt_lt || apply Z.lt_gt || apply Z.le_ge || apply Z.ge_le; assumption.

Ltac Falsum :=
  try intro; apply False_ind;
   repeat
    match goal with
    | id1:(~ ?X1) |- ?X2 =>
        (apply id1; assumption || reflexivity) || clear id1
    end.


Ltac Step_l a :=
  match goal with
  |  |- (?X1 < ?X2)%Z => replace X1 with a; [ idtac | try ring ]
  end.

Ltac Step_r a :=
  match goal with
  |  |- (?X1 < ?X2)%Z => replace X2 with a; [ idtac | try ring ]
  end.

Ltac CaseEq formula :=
  generalize (refl_equal formula); pattern formula at -1 in |- *;
   case formula.


Lemma pair_1 : forall (A B : Set) (H : A * B), H = pair (fst H) (snd H).
Proof.
 intros.
 case H.
 intros.
 simpl in |- *.
 reflexivity.
Qed.

Lemma pair_2 :
 forall (A B : Set) (H1 H2 : A * B),
 fst H1 = fst H2 -> snd H1 = snd H2 -> H1 = H2.
Proof.
 intros A B H1 H2.
 case H1.
 case H2.
 simpl in |- *.
 intros.
 rewrite H.
 rewrite H0.
 reflexivity.
Qed.


Section projection.
 Variable A : Set.
 Variable P : A -> Prop.

 Definition projP1 (H : sig P) := let (x, h) := H in x.
 Definition projP2 (H : sig P) :=
   let (x, h) as H return (P (projP1 H)) := H in h.
End projection.


(*###########################################################################*)
(* Declaring some realtions on natural numbers for stepl and stepr tactics.  *)
(*###########################################################################*)

Lemma le_stepl: forall x y z, le x y -> x=z -> le z y.
Proof.
 intros x y z H_le H_eq; subst z; trivial.
Qed.

Lemma le_stepr: forall x y z, le x y -> y=z -> le x z.
Proof.
 intros x y z H_le H_eq; subst z; trivial.
Qed.

Lemma lt_stepl: forall x y z, lt x y -> x=z -> lt z y.
Proof.
 intros x y z H_lt H_eq; subst z; trivial.
Qed.

Lemma lt_stepr: forall x y z, lt x y -> y=z -> lt x z.
Proof.
 intros x y z H_lt H_eq; subst z; trivial.
Qed.

Lemma neq_stepl:forall (x y z:nat), x<>y -> x=z -> z<>y.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Qed.

Lemma neq_stepr:forall (x y z:nat), x<>y -> y=z -> x<>z.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Qed.


Declare Left Step le_stepl.
Declare Right Step le_stepr.
Declare Left Step lt_stepl.
Declare Right Step lt_stepr.
Declare Left Step neq_stepl.
Declare Right Step neq_stepr.

(*###########################################################################*)
(** Some random facts about natural numbers, positive numbers and integers   *)
(*###########################################################################*)


Lemma not_O_S : forall n : nat, n <> 0 -> {p : nat | n = S p}.
Proof.
 intros [| np] Hn; [ exists 0; apply False_ind; apply Hn | exists np ];
  reflexivity.
Qed.


Lemma lt_minus_neq : forall m n : nat, m < n -> n - m <> 0.
Proof.
 intros.
 omega.
Qed.

Lemma lt_minus_eq_0 : forall m n : nat, m < n -> m - n = 0.
Proof.
 intros.
 omega.
Qed.

Lemma le_plus_Sn_1_SSn : forall n : nat, S n + 1 <= S (S n).
Proof.
 intros.
 omega.
Qed.

Lemma le_plus_O_l : forall p q : nat, p + q <= 0 -> p = 0.
Proof.
 intros; omega.
Qed.

Lemma le_plus_O_r : forall p q : nat, p + q <= 0 -> q = 0.
Proof.
 intros; omega.
Qed.

Lemma minus_pred : forall m n : nat, 0 < n -> pred m - pred n = m - n.
Proof.
 intros.
 omega.
Qed.


(*###########################################################################*)
(* Declaring some realtions on integers for stepl and stepr tactics.         *)
(*###########################################################################*)

Lemma Zle_stepl: forall x y z, (x<=y)%Z -> x=z -> (z<=y)%Z.
Proof.
 intros x y z H_le H_eq; subst z; trivial.
Qed.

Lemma Zle_stepr: forall x y z, (x<=y)%Z -> y=z -> (x<=z)%Z.
Proof.
 intros x y z H_le H_eq; subst z; trivial.
Qed.

Lemma Zlt_stepl: forall x y z, (x<y)%Z -> x=z -> (z<y)%Z.
Proof.
 intros x y z H_lt H_eq; subst z; trivial.
Qed.

Lemma Zlt_stepr: forall x y z, (x<y)%Z -> y=z -> (x<z)%Z.
Proof.
 intros x y z H_lt H_eq; subst z; trivial.
Qed.

Lemma Zneq_stepl:forall (x y z:Z), (x<>y)%Z -> x=z -> (z<>y)%Z.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Qed.

Lemma Zneq_stepr:forall (x y z:Z), (x<>y)%Z -> y=z -> (x<>z)%Z.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Qed.

Declare Left Step Zle_stepl.
Declare Right Step Zle_stepr.
Declare Left Step Zlt_stepl.
Declare Right Step Zlt_stepr.
Declare Left Step Zneq_stepl.
Declare Right Step Zneq_stepr.


(*###########################################################################*)
(** Informative case analysis                                                *)
(*###########################################################################*)

Lemma Zlt_cotrans :
 forall x y : Z, (x < y)%Z -> forall z : Z, {(x < z)%Z} + {(z < y)%Z}.
Proof.
 intros.
 case (Z_lt_ge_dec x z).
 intro.
 left.
 assumption.
 intro.
 right.
 apply Z.le_lt_trans with (m := x).
 apply Z.ge_le.
 assumption.
 assumption.
Qed.

Lemma Zlt_cotrans_pos :
 forall x y : Z, (0 < x + y)%Z -> {(0 < x)%Z} + {(0 < y)%Z}.
Proof.
 intros.
 case (Zlt_cotrans 0 (x + y) H x).
 intro.
 left.
 assumption.
 intro.
 right.
 apply Zplus_lt_reg_l with (p := x).
 rewrite Zplus_0_r.
 assumption.
Qed.


Lemma Zlt_cotrans_neg :
 forall x y : Z, (x + y < 0)%Z -> {(x < 0)%Z} + {(y < 0)%Z}.
Proof.
 intros x y H; case (Zlt_cotrans (x + y) 0 H x); intro Hxy;
  [ right; apply Zplus_lt_reg_l with (p := x); rewrite Zplus_0_r | left ];
  assumption.
Qed.



Lemma not_Zeq_inf : forall x y : Z, x <> y -> {(x < y)%Z} + {(y < x)%Z}.
Proof.
 intros.
 case Z_lt_ge_dec with x y.
 intro.
 left.
 assumption.
 intro H0.
 generalize (Z.ge_le _ _ H0).
 intro.
 case (Z_le_lt_eq_dec _ _ H1).
 intro.
 right.
 assumption.
 intro.
 apply False_rec.
 apply H.
 symmetry  in |- *.
 assumption.
Qed.

Lemma Z_dec : forall x y : Z, {(x < y)%Z} + {(x > y)%Z} + {x = y}.
Proof.
 intros.
 case (Z_lt_ge_dec x y).
 intro H.
 left.
 left.
 assumption.
 intro H.
 generalize (Z.ge_le _ _ H).
 intro H0.
 case (Z_le_lt_eq_dec y x H0).
 intro H1.
 left.
 right.
 apply Z.lt_gt.
 assumption.
 intro.
 right.
 symmetry  in |- *.
 assumption.
Qed.


Lemma Z_dec' : forall x y : Z, {(x < y)%Z} + {(y < x)%Z} + {x = y}.
Proof.
 intros x y.
 case (Z.eq_dec x y); intro H;
  [ right; assumption | left; apply (not_Zeq_inf _ _ H) ].
Qed.

Lemma Z_lt_le_dec : forall x y : Z, {(x < y)%Z} + {(y <= x)%Z}.
Proof.
 intros.
 case (Z_lt_ge_dec x y).
 intro.
 left.
 assumption.
 intro.
 right.
 apply Z.ge_le.
 assumption.
Qed.

Lemma Z_le_lt_dec : forall x y : Z, {(x <= y)%Z} + {(y < x)%Z}.
Proof.
 intros; case (Z_lt_le_dec y x); [ right | left ]; assumption.
Qed.

Lemma Z_lt_lt_S_eq_dec :
 forall x y : Z, (x < y)%Z -> {(x + 1 < y)%Z} + {(x + 1)%Z = y}.
Proof.
 intros.
 generalize (Zlt_le_succ _ _ H).
 unfold Z.succ in |- *.
 apply Z_le_lt_eq_dec.
Qed.

Lemma quadro_leq_inf :
 forall a b c d : Z,
 {(c <= a)%Z /\ (d <= b)%Z} + {~ ((c <= a)%Z /\ (d <= b)%Z)}.
Proof.
 intros.
 case (Z_lt_le_dec a c).
 intro z.
 right.
 intro.
 elim H.
 intros.
 generalize z.
 apply Zle_not_lt.
 assumption.
 intro.
 case (Z_lt_le_dec b d).
 intro z0.
 right.
 intro.
 elim H.
 intros.
 generalize z0.
 apply Zle_not_lt.
 assumption.
 intro.
 left.
 split.
 assumption.
 assumption.
Qed.

(*###########################################################################*)
(** General auxiliary lemmata                                                *)
(*###########################################################################*)

Lemma Zminus_eq : forall x y : Z, (x - y)%Z = 0%Z -> x = y.
Proof.
 intros.
 apply Zplus_reg_l with (- y)%Z.
 rewrite Zplus_opp_l.
 unfold Zminus in H.
 rewrite Zplus_comm.
 assumption.
Qed.

Lemma Zlt_minus : forall a b : Z, (b < a)%Z -> (0 < a - b)%Z.
Proof.
 intros a b.
 intros.
 apply Zplus_lt_reg_l with b.
 unfold Zminus in |- *.
 rewrite (Zplus_comm a).
 rewrite (Zplus_assoc b (- b)).
 rewrite Zplus_opp_r.
 simpl in |- *.
 rewrite <- Zplus_0_r_reverse.
 assumption.
Qed.


Lemma Zle_minus : forall a b : Z, (b <= a)%Z -> (0 <= a - b)%Z.
Proof.
 intros a b.
 intros.
 apply Zplus_le_reg_l with b.
 unfold Zminus in |- *.
 rewrite (Zplus_comm a).
 rewrite (Zplus_assoc b (- b)).
 rewrite Zplus_opp_r.
 simpl in |- *.
 rewrite <- Zplus_0_r_reverse.
 assumption.
Qed.

Lemma Zlt_plus_plus :
 forall m n p q : Z, (m < n)%Z -> (p < q)%Z -> (m + p < n + q)%Z.
Proof.
 intros.
 apply Z.lt_trans with (m := (n + p)%Z).
 rewrite Zplus_comm.
 rewrite Zplus_comm with (n := n).
 apply Zplus_lt_compat_l.
 assumption.
 apply Zplus_lt_compat_l.
 assumption.
Qed.

Lemma Zgt_plus_plus :
 forall m n p q : Z, (m > n)%Z -> (p > q)%Z -> (m + p > n + q)%Z.
 intros.
 apply Zgt_trans with (m := (n + p)%Z).
 rewrite Zplus_comm.
 rewrite Zplus_comm with (n := n).
 apply Zplus_gt_compat_l.
 assumption.
 apply Zplus_gt_compat_l.
 assumption.
Qed.

Lemma Zle_lt_plus_plus :
 forall m n p q : Z, (m <= n)%Z -> (p < q)%Z -> (m + p < n + q)%Z.
Proof.
 intros.
 case (Zle_lt_or_eq m n).
 assumption.
 intro.
 apply Zlt_plus_plus.
 assumption.
 assumption.
 intro.
 rewrite H1.
 apply Zplus_lt_compat_l.
 assumption.
Qed.

Lemma Zge_gt_plus_plus :
 forall m n p q : Z, (m >= n)%Z -> (p > q)%Z -> (m + p > n + q)%Z.
Proof.
 intros.
 case (Zle_lt_or_eq n m).
 apply Z.ge_le.
 assumption.
 intro.
 apply Zgt_plus_plus.
 apply Z.lt_gt.
 assumption.
 assumption.
 intro.
 rewrite H1.
 apply Zplus_gt_compat_l.
 assumption.
Qed.

Lemma Zgt_ge_plus_plus :
 forall m n p q : Z, (m > n)%Z -> (p >= q)%Z -> (m + p > n + q)%Z.
Proof.
 intros.
 rewrite Zplus_comm.
 replace (n + q)%Z with (q + n)%Z.
 apply Zge_gt_plus_plus.
 assumption.
 assumption.
 apply Zplus_comm.
Qed.

Lemma Zlt_resp_pos : forall x y : Z, (0 < x)%Z -> (0 < y)%Z -> (0 < x + y)%Z.
Proof.
 intros.
 rewrite <- Zplus_0_r with 0%Z.
 apply Zlt_plus_plus; assumption.
Qed.


Lemma Zle_resp_neg :
 forall x y : Z, (x <= 0)%Z -> (y <= 0)%Z -> (x + y <= 0)%Z.
Proof.
 intros.
 rewrite <- Zplus_0_r with 0%Z.
 apply Zplus_le_compat; assumption.
Qed.


Lemma Zlt_pos_opp : forall x : Z, (0 < x)%Z -> (- x < 0)%Z.
Proof.
 intros.
 apply Zplus_lt_reg_l with x.
 rewrite Zplus_opp_r.
 rewrite Zplus_0_r.
 assumption.
Qed.

Lemma Zlt_neg_opp : forall x : Z, (x < 0)%Z -> (0 < - x)%Z.
Proof.
 intros.
 apply Zplus_lt_reg_l with x.
 rewrite Zplus_opp_r.
 rewrite Zplus_0_r.
 assumption.
Qed.


Lemma Zle_neg_opp : forall x : Z, (x <= 0)%Z -> (0 <= - x)%Z.
Proof.
 intros.
 apply Zplus_le_reg_l with x.
 rewrite Zplus_opp_r.
 rewrite Zplus_0_r.
 assumption.
Qed.

Lemma Zle_pos_opp : forall x : Z, (0 <= x)%Z -> (- x <= 0)%Z.
Proof.
 intros.
 apply Zplus_le_reg_l with x.
 rewrite Zplus_opp_r.
 rewrite Zplus_0_r.
 assumption.
Qed.


Lemma Zge_opp : forall x y : Z, (x <= y)%Z -> (- x >= - y)%Z.
Proof.
 intros.
 apply Z.le_ge.
 apply Zplus_le_reg_l with (p := (x + y)%Z).
 ring_simplify (x + y + - y)%Z (x + y + - x)%Z.
 assumption.
Qed.



(* Omega can't solve this *)
Lemma Zmult_pos_pos : forall x y : Z, (0 < x)%Z -> (0 < y)%Z -> (0 < x * y)%Z.
Proof.
 intros [| px| px] [| py| py] Hx Hy; trivial || constructor.
Qed.

Lemma Zmult_neg_neg : forall x y : Z, (x < 0)%Z -> (y < 0)%Z -> (0 < x * y)%Z.
Proof.
 intros [| px| px] [| py| py] Hx Hy; trivial || constructor.
Qed.

Lemma Zmult_neg_pos : forall x y : Z, (x < 0)%Z -> (0 < y)%Z -> (x * y < 0)%Z.
Proof.
 intros [| px| px] [| py| py] Hx Hy; trivial || constructor.
Qed.

Lemma Zmult_pos_neg : forall x y : Z, (0 < x)%Z -> (y < 0)%Z -> (x * y < 0)%Z.
Proof.
 intros [| px| px] [| py| py] Hx Hy; trivial || constructor.
Qed.



Hint Resolve Zmult_pos_pos Zmult_neg_neg Zmult_neg_pos Zmult_pos_neg: zarith.


Lemma Zle_reg_mult_l :
 forall x y a : Z, (0 < a)%Z -> (x <= y)%Z -> (a * x <= a * y)%Z.
Proof.
 intros.
 apply Zplus_le_reg_l with (p := (- a * x)%Z).
 ring_simplify (- a * x + a * x)%Z.
 replace (- a * x + a * y)%Z with ((y - x) * a)%Z.
 apply Zmult_gt_0_le_0_compat.
 apply Z.lt_gt.
 assumption.
 unfold Zminus in |- *.
 apply Zle_left.
 assumption.
 ring.
Qed.

Lemma Zsimpl_plus_l_dep :
 forall x y m n : Z, (x + m)%Z = (y + n)%Z -> x = y -> m = n.
Proof.
 intros.
 apply Zplus_reg_l with x.
 rewrite <- H0 in H.
 assumption.
Qed.


Lemma Zsimpl_plus_r_dep :
 forall x y m n : Z, (m + x)%Z = (n + y)%Z -> x = y -> m = n.
Proof.
 intros.
 apply Zplus_reg_l with x.
 rewrite Zplus_comm.
 rewrite Zplus_comm with x n.
 rewrite <- H0 in H.
 assumption.
Qed.

Lemma Zmult_simpl :
 forall n m p q : Z, n = m -> p = q -> (n * p)%Z = (m * q)%Z.
Proof.
 intros.
 rewrite H.
 rewrite H0.
 reflexivity.
Qed.

Lemma Zsimpl_mult_l :
 forall n m p : Z, n <> 0%Z -> (n * m)%Z = (n * p)%Z -> m = p.
Proof.
 intros.
 apply Zplus_reg_l with (n := (- p)%Z).
 replace (- p + p)%Z with 0%Z.
 apply Zmult_integral_l with (n := n).
 assumption.
 replace ((- p + m) * n)%Z with (n * m + - (n * p))%Z.
 apply Zegal_left.
 assumption.
 ring.
 ring.
Qed.

Lemma Zlt_reg_mult_l :
 forall x y z : Z, (x > 0)%Z -> (y < z)%Z -> (x * y < x * z)%Z. (*QA*)
Proof.
 intros.
 case (Zcompare_Gt_spec x 0).
 unfold Z.gt in H.
 assumption.
 intros.
 cut (x = Zpos x0).
 intro.
 rewrite H2.
 unfold Z.lt in H0.
 unfold Z.lt in |- *.
 cut ((Zpos x0 * y ?= Zpos x0 * z)%Z = (y ?= z)%Z).
 intro.
 exact (trans_eq H3 H0).
 apply Zcompare_mult_compat.
 cut (x = (x + - (0))%Z).
 intro.
 exact (trans_eq H2 H1).
 simpl in |- *.
 apply (sym_eq (A:=Z)).
 exact (Zplus_0_r x).
Qed.


Lemma Zlt_opp : forall x y : Z, (x < y)%Z -> (- x > - y)%Z. (*QA*)
Proof.
 intros.
 red in |- *.
 apply sym_eq.
 cut (Datatypes.Gt = (y ?= x)%Z).
 intro.
 cut ((y ?= x)%Z = (- x ?= - y)%Z).
 intro.
 exact (trans_eq H0 H1).
 exact (Zcompare_opp y x).
 apply sym_eq.
 exact (Z.lt_gt x y H).
Qed.


Lemma Zlt_conv_mult_l :
 forall x y z : Z, (x < 0)%Z -> (y < z)%Z -> (x * y > x * z)%Z. (*QA*)
Proof.
 intros.
 cut (- x > 0)%Z.
 intro.
 cut (- x * y < - x * z)%Z.
 intro.
 cut (- (- x * y) > - (- x * z))%Z.
 intro.
 cut (- - (x * y) > - - (x * z))%Z.
 intro.
 cut ((- - (x * y))%Z = (x * y)%Z).
 intro.
 rewrite H5 in H4.
 cut ((- - (x * z))%Z = (x * z)%Z).
 intro.
 rewrite H6 in H4.
 assumption.
 exact (Z.opp_involutive (x * z)).
 exact (Z.opp_involutive (x * y)).
 cut ((- (- x * y))%Z = (- - (x * y))%Z).
 intro.
 rewrite H4 in H3.
 cut ((- (- x * z))%Z = (- - (x * z))%Z).
 intro.
 rewrite H5 in H3.
 assumption.
 cut ((- x * z)%Z = (- (x * z))%Z).
 intro.
 exact (f_equal Z.opp H5).
 exact (Zopp_mult_distr_l_reverse x z).
 cut ((- x * y)%Z = (- (x * y))%Z).
 intro.
 exact (f_equal Z.opp H4).
 exact (Zopp_mult_distr_l_reverse x y).
 exact (Zlt_opp (- x * y) (- x * z) H2).
 exact (Zlt_reg_mult_l (- x) y z H1 H0).
 exact (Zlt_opp x 0 H).
Qed.

Lemma Zgt_not_eq : forall x y : Z, (x > y)%Z -> x <> y.   (*QA*)
Proof.
 intros.
 cut (y < x)%Z.
 intro.
 cut (y <> x).
 intro.
 red in |- *.
 intros.
 cut (y = x).
 intros.
 apply H1.
 assumption.
 exact (sym_eq H2).
 exact (Zorder.Zlt_not_eq y x H0).
 exact (Z.gt_lt x y H).
Qed.

Lemma Zmult_resp_nonzero :
 forall x y : Z, x <> 0%Z -> y <> 0%Z -> (x * y)%Z <> 0%Z.
Proof.
 intros x y Hx Hy Hxy.
 apply Hx.
 apply Zmult_integral_l with y; assumption.
Qed.


Lemma Zopp_app : forall y : Z, y <> 0%Z -> (- y)%Z <> 0%Z.
Proof.
 intros.
 intro.
 apply H.
 apply Zplus_reg_l with (- y)%Z.
 rewrite Zplus_opp_l.
 rewrite H0.
 simpl in |- *.
 reflexivity.
Qed.


Lemma Zle_neq_Zlt : forall a b : Z, (a <= b)%Z -> b <> a -> (a < b)%Z.
Proof.
 intros a b H H0.
 case (Z_le_lt_eq_dec _ _ H); trivial.
 intro; apply False_ind; apply H0; symmetry  in |- *; assumption.
Qed.

Lemma not_Zle_lt : forall x y : Z, ~ (y <= x)%Z -> (x < y)%Z.
Proof.
 intros; apply Z.gt_lt; apply Znot_le_gt; assumption.
Qed.

Lemma not_Zlt : forall x y : Z, ~ (y < x)%Z -> (x <= y)%Z.
Proof.
 intros x y H1 H2; apply H1; apply Z.gt_lt; assumption.
Qed.


Lemma Zmult_absorb :
 forall x y z : Z, x <> 0%Z -> (x * y)%Z = (x * z)%Z -> y = z.  (*QA*)
Proof.
 intros.
 case (dec_eq y z).
 intro.
 assumption.
 intro.
 case (not_Zeq y z).
 assumption.
 intro.
 case (not_Zeq x 0).
 assumption.
 intro.
 apply False_ind.
 cut (x * y > x * z)%Z.
 intro.
 cut ((x * y)%Z <> (x * z)%Z).
 intro.
 apply H5.
 assumption.
 exact (Zgt_not_eq (x * y) (x * z) H4).
 exact (Zlt_conv_mult_l x y z H3 H2).
 intro.
 apply False_ind.
 cut (x * y < x * z)%Z.
 intro.
 cut ((x * y)%Z <> (x * z)%Z).
 intro.
 apply H5.
 assumption.
 exact (Zorder.Zlt_not_eq (x * y) (x * z) H4).
 cut (x > 0)%Z.
 intro.
 exact (Zlt_reg_mult_l x y z H4 H2).
 exact (Z.lt_gt 0 x H3).
 intro.
 apply False_ind.
 cut (x * z < x * y)%Z.
 intro.
 cut ((x * z)%Z <> (x * y)%Z).
 intro.
 apply H4.
 apply (sym_eq (A:=Z)).
 assumption.
 exact (Zorder.Zlt_not_eq (x * z) (x * y) H3).
 apply False_ind.
 case (not_Zeq x 0).
 assumption.
 intro.
 cut (x * z > x * y)%Z.
 intro.
 cut ((x * z)%Z <> (x * y)%Z).
 intro.
 apply H5.
 apply (sym_eq (A:=Z)).
 assumption.
 exact (Zgt_not_eq (x * z) (x * y) H4).
 exact (Zlt_conv_mult_l x z y H3 H2).
 intro.
 cut (x * z < x * y)%Z.
 intro.
 cut ((x * z)%Z <> (x * y)%Z).
 intro.
 apply H5.
 apply (sym_eq (A:=Z)).
 assumption.
 exact (Zorder.Zlt_not_eq (x * z) (x * y) H4).
 cut (x > 0)%Z.
 intro.
 exact (Zlt_reg_mult_l x z y H4 H2).
 exact (Z.lt_gt 0 x H3).
Qed.

Lemma Zlt_mult_mult :
 forall a b c d : Z,
 (0 < a)%Z -> (0 < d)%Z -> (a < b)%Z -> (c < d)%Z -> (a * c < b * d)%Z.
Proof.
 intros.
 apply Z.lt_trans with (a * d)%Z.
 apply Zlt_reg_mult_l.
 Flip.
 assumption.
 rewrite Zmult_comm.
 rewrite Zmult_comm with b d.
 apply Zlt_reg_mult_l.
 Flip.
 assumption.
Qed.

Lemma Zgt_mult_conv_absorb_l :
 forall a x y : Z, (a < 0)%Z -> (a * x > a * y)%Z -> (x < y)%Z. (*QC*)
Proof.
 intros.
 case (dec_eq x y).
 intro.
 apply False_ind.
 rewrite H1 in H0.
 cut ((a * y)%Z = (a * y)%Z).
 change ((a * y)%Z <> (a * y)%Z) in |- *.
 apply Zgt_not_eq.
 assumption.
 trivial.

 intro.
 case (not_Zeq x y H1).
 trivial.

 intro.
 apply False_ind.
 cut (a * y > a * x)%Z.
 apply Zgt_asym with (m := (a * y)%Z) (n := (a * x)%Z).
 assumption.
 apply Zlt_conv_mult_l.
 assumption.
 assumption.
Qed.

Lemma Zgt_mult_reg_absorb_l :
 forall a x y : Z, (a > 0)%Z -> (a * x > a * y)%Z -> (x > y)%Z. (*QC*)
Proof.
 intros.
 cut (- - a > - - (0))%Z.
 intro.
 cut (- a < - (0))%Z.
 simpl in |- *.
 intro.
 replace x with (- - x)%Z.
 replace y with (- - y)%Z.
 apply Zlt_opp.
 apply Zgt_mult_conv_absorb_l with (a := (- a)%Z) (x := (- x)%Z).
 assumption.
 rewrite Zmult_opp_opp.
 rewrite Zmult_opp_opp.
 assumption.
 apply Z.opp_involutive.
 apply Z.opp_involutive.
 apply Z.gt_lt.
 apply Zlt_opp.
 apply Z.gt_lt.
 assumption.
 simpl in |- *.
 rewrite Z.opp_involutive.
 assumption.
Qed.

Lemma Zopp_Zlt : forall x y : Z, (y < x)%Z -> (- x < - y)%Z.
Proof.
 intros x y Hyx.
 apply Zgt_mult_conv_absorb_l with (a := (-1)%Z).
 constructor.
 replace (-1 * - y)%Z with y.
 replace (-1 * - x)%Z with x.
 Flip.
 ring.
 ring.
Qed.


Lemma Zmin_cancel_Zlt : forall x y : Z, (- x < - y)%Z -> (y < x)%Z.
Proof.
 intros.
 apply Zgt_mult_conv_absorb_l with (a := (-1)%Z).
 constructor.
 replace (-1 * y)%Z with (- y)%Z.
 replace (-1 * x)%Z with (- x)%Z.
 apply Z.lt_gt.
 assumption.
 ring.
 ring.
Qed.


Lemma Zmult_cancel_Zle :
 forall a x y : Z, (a < 0)%Z -> (a * x <= a * y)%Z -> (y <= x)%Z.
Proof.
 intros.
 case (Z_le_gt_dec y x).
 trivial.
 intro.
 apply False_ind.
 apply (Z.lt_irrefl (a * x)).
 apply Z.le_lt_trans with (m := (a * y)%Z).
 assumption.
 apply Z.gt_lt.
 apply Zlt_conv_mult_l.
 assumption.
 apply Z.gt_lt.
 assumption.
Qed.

Lemma Zlt_mult_cancel_l :
 forall x y z : Z, (0 < x)%Z -> (x * y < x * z)%Z -> (y < z)%Z.
Proof.
 intros.
 apply Z.gt_lt.
 apply Zgt_mult_reg_absorb_l with x.
 apply Z.lt_gt.
 assumption.
 apply Z.lt_gt.
 assumption.
Qed.


Lemma Zmin_cancel_Zle : forall x y : Z, (- x <= - y)%Z -> (y <= x)%Z.
Proof.
 intros.
 apply Zmult_cancel_Zle with (a := (-1)%Z).
 constructor.
 replace (-1 * y)%Z with (- y)%Z.
 replace (-1 * x)%Z with (- x)%Z.
 assumption.
 ring.
 ring.
Qed.



Lemma Zmult_resp_Zle :
 forall a x y : Z, (0 < a)%Z -> (a * y <= a * x)%Z -> (y <= x)%Z.
Proof.
 intros.
 case (Z_le_gt_dec y x).
 trivial.
 intro.
 apply False_ind.
 apply (Z.lt_irrefl (a * y)).
 apply Z.le_lt_trans with (m := (a * x)%Z).
 assumption.
 apply Zlt_reg_mult_l.
 apply Z.lt_gt.
 assumption.
 apply Z.gt_lt.
 assumption.
Qed.

Lemma Zopp_Zle : forall x y : Z, (y <= x)%Z -> (- x <= - y)%Z.
Proof.
 intros.
 apply Zmult_cancel_Zle with (a := (-1)%Z).
 constructor.
 replace (-1 * - y)%Z with y.
 replace (-1 * - x)%Z with x.
 assumption.
 clear y H; ring.
 clear x H; ring.
Qed.


Lemma Zle_lt_eq_S : forall x y : Z, (x <= y)%Z -> (y < x + 1)%Z -> y = x.
Proof.
 intros.
 case (Z_le_lt_eq_dec x y H).
 intro H1.
 apply False_ind.
 generalize (Zlt_le_succ x y H1).
 intro.
 apply (Zlt_not_le y (x + 1) H0).
 replace (x + 1)%Z with (Z.succ x).
 assumption.
 reflexivity.
 intro H1.
 symmetry  in |- *.
 assumption.
Qed.

Lemma Zlt_le_eq_S :
 forall x y : Z, (x < y)%Z -> (y <= x + 1)%Z -> y = (x + 1)%Z.
Proof.
 intros.
 case (Z_le_lt_eq_dec y (x + 1) H0).
 intro H1.
 apply False_ind.
 generalize (Zlt_le_succ x y H).
 intro.
 apply (Zlt_not_le y (x + 1) H1).
 replace (x + 1)%Z with (Z.succ x).
 assumption.
 reflexivity.
 trivial.
Qed.


Lemma double_not_equal_zero :
 forall c d : Z, ~ (c = 0%Z /\ d = 0%Z) -> c <> d \/ c <> 0%Z.
Proof.
 intros.
 case (Z_zerop c).
 intro.
 rewrite e.
 left.
 apply sym_not_eq.
 intro.
 apply H; repeat split; assumption.
 intro; right; assumption.
Qed.

Lemma triple_not_equal_zero :
 forall a b c : Z,
 ~ (a = 0%Z /\ b = 0%Z /\ c = 0%Z) -> a <> 0%Z \/ b <> 0%Z \/ c <> 0%Z.
Proof.
 intros a b c H; case (Z_zerop a); intro Ha;
            [ case (Z_zerop b); intro Hb;
               [ case (Z_zerop c); intro Hc;
                  [ apply False_ind; apply H; repeat split | right; right ]
               | right; left ]
            | left ]; assumption.
Qed.

Lemma mediant_1 :
 forall m n m' n' : Z, (m' * n < m * n')%Z -> ((m + m') * n < m * (n + n'))%Z.
Proof.
 intros.
 rewrite Zmult_plus_distr_r.
 rewrite Zmult_plus_distr_l.
 apply Zplus_lt_compat_l.
 assumption.
Qed.

Lemma mediant_2 :
 forall m n m' n' : Z,
 (m' * n < m * n')%Z -> (m' * (n + n') < (m + m') * n')%Z.
Proof.
 intros.
 rewrite Zmult_plus_distr_l.
 rewrite Zmult_plus_distr_r.
 apply Zplus_lt_compat_r.
 assumption.
Qed.


Lemma mediant_3 :
 forall a b m n m' n' : Z,
 (0 <= a * m + b * n)%Z ->
 (0 <= a * m' + b * n')%Z -> (0 <= a * (m + m') + b * (n + n'))%Z.
Proof.
 intros.
 replace (a * (m + m') + b * (n + n'))%Z with
  (a * m + b * n + (a * m' + b * n'))%Z.
 apply Zplus_le_0_compat.
 assumption.
 assumption.
 ring.
Qed.

Lemma fraction_lt_trans :
 forall a b c d e f : Z,
 (0 < b)%Z ->
 (0 < d)%Z ->
 (0 < f)%Z -> (a * d < c * b)%Z -> (c * f < e * d)%Z -> (a * f < e * b)%Z.
Proof.
 intros.
 apply Z.gt_lt.
 apply Zgt_mult_reg_absorb_l with d.
 Flip.
 apply Zgt_trans with (c * b * f)%Z.
 replace (d * (e * b))%Z with (b * (e * d))%Z.
 replace (c * b * f)%Z with (b * (c * f))%Z.
 apply Z.lt_gt.
 apply Zlt_reg_mult_l.
 Flip.
 assumption.
 ring.
 ring.
 replace (c * b * f)%Z with (f * (c * b))%Z.
 replace (d * (a * f))%Z with (f * (a * d))%Z.
 apply Z.lt_gt.
 apply Zlt_reg_mult_l.
 Flip.
 assumption.
 ring.
 ring.
Qed.


Lemma square_pos : forall a : Z, a <> 0%Z -> (0 < a * a)%Z.
Proof.
 intros [| p| p]; intros; [ Falsum | constructor | constructor ].
Qed.

Hint Resolve square_pos: zarith.

(*###########################################################################*)
(** Properties of positive numbers, mapping between Z and nat                *)
(*###########################################################################*)


Definition Z2positive (z : Z) :=
  match z with
  | Zpos p => p
  | Zneg p => p
  | Z0 => 1%positive
  end.


Lemma ZL9 : forall p : positive, Z_of_nat (nat_of_P p) = Zpos p. (*QF*)
Proof.
 intro.
 cut (exists h : nat, nat_of_P p = S h).
 intro.
 case H.
 intros.
 unfold Z_of_nat in |- *.
 rewrite H0.

 apply f_equal with (A := positive) (B := Z) (f := Zpos).
 cut (P_of_succ_nat (nat_of_P p) = P_of_succ_nat (S x)).
 intro.
 rewrite P_of_succ_nat_o_nat_of_P_eq_succ in H1.
 cut (Pos.pred (Pos.succ p) = Pos.pred (P_of_succ_nat (S x))).
 intro.
 rewrite Pos.pred_succ in H2.
 simpl in H2.
 rewrite Pos.pred_succ in H2.
 apply sym_eq.
 assumption.
 apply f_equal with (A := positive) (B := positive) (f := Pos.pred).
 assumption.
 apply f_equal with (f := P_of_succ_nat).
 assumption.
 apply ZL4.
Qed.

Coercion Z_of_nat : nat >-> Z.

Lemma ZERO_lt_POS : forall p : positive, (0 < Zpos p)%Z.
Proof.
 intros.
 constructor.
Qed.


Lemma POS_neq_ZERO : forall p : positive, Zpos p <> 0%Z.
Proof.
 intros.
 apply sym_not_eq.
 apply Zorder.Zlt_not_eq.
 apply ZERO_lt_POS.
Qed.

Lemma NEG_neq_ZERO : forall p : positive, Zneg p <> 0%Z.
Proof.
 intros.
 apply Zorder.Zlt_not_eq.
 unfold Z.lt in |- *.
 constructor.
Qed.


Lemma POS_resp_eq : forall p0 p1 : positive, Zpos p0 = Zpos p1 -> p0 = p1.
Proof.
 intros.
 injection H.
 trivial.
Qed.

Lemma nat_nat_pos : forall m n : nat, ((m + 1) * (n + 1) > 0)%Z. (*QF*)
Proof.
 intros.
 apply Z.lt_gt.
 cut (Z_of_nat m + 1 > 0)%Z.
 intro.
 cut (0 < Z_of_nat n + 1)%Z.
 intro.
 cut ((Z_of_nat m + 1) * 0 < (Z_of_nat m + 1) * (Z_of_nat n + 1))%Z.
 rewrite Zmult_0_r.
 intro.
 assumption.

 apply Zlt_reg_mult_l.
 assumption.
 assumption.
 change (0 < Z.succ (Z_of_nat n))%Z in |- *.
 apply Zle_lt_succ.
 change (Z_of_nat 0 <= Z_of_nat n)%Z in |- *.
 apply Znat.inj_le.
 apply le_O_n.
 apply Z.lt_gt.
 change (0 < Z.succ (Z_of_nat m))%Z in |- *.
 apply Zle_lt_succ.
 change (Z_of_nat 0 <= Z_of_nat m)%Z in |- *.
 apply Znat.inj_le.
 apply le_O_n.
Qed.


Theorem S_predn : forall m : nat, m <> 0 -> S (pred m) = m. (*QF*)
Proof.
 intros.
 case (O_or_S m).
 intro.
 case s.
 intros.
 rewrite <- e.
 rewrite <- pred_Sn with (n := x).
 trivial.
 intro.
 apply False_ind.
 apply H.
 apply sym_eq.
 assumption.
Qed.

Lemma absolu_1 : forall x : Z, Z.abs_nat x = 0 -> x = 0%Z. (*QF*)
Proof.
 intros.
 case (dec_eq x 0).
 intro.
 assumption.
 intro.
 apply False_ind.
 cut ((x < 0)%Z \/ (x > 0)%Z).
 intro.
 ElimCompare x 0%Z.
 intro.
 cut (x = 0%Z).
 assumption.
 cut ((x ?= 0)%Z = Datatypes.Eq -> x = 0%Z).
 intro.
 apply H3.
 assumption.
 apply proj1 with (B := x = 0%Z -> (x ?= 0)%Z = Datatypes.Eq).
 change ((x ?= 0)%Z = Datatypes.Eq <-> x = 0%Z) in |- *.
 apply Zcompare_Eq_iff_eq.

 (***)
 intro.
 cut (exists h : nat, Z.abs_nat x = S h).
 intro.
 case H3.
 rewrite H.
 exact O_S.

 change (x < 0)%Z in H2.
 cut (0 > x)%Z.
 intro.
 cut (exists p : positive, (0 + - x)%Z = Zpos p).
 simpl in |- *.
 intro.
 case H4.
 intros.
 cut (exists q : positive, x = Zneg q).
 intro.
 case H6.
 intros.
 rewrite H7.
 unfold Z.abs_nat in |- *.
 generalize x1.
 exact ZL4.
 cut (x = (- Zpos x0)%Z).
 simpl in |- *.
 intro.
 exists x0.
 assumption.
 cut ((- - x)%Z = x).
 intro.
 rewrite <- H6.
 exact (f_equal Z.opp H5).
 apply Z.opp_involutive.
 apply Zcompare_Gt_spec.
 assumption.
 apply Z.lt_gt.
 assumption.

 (***)
 intro.
 cut (exists h : nat, Z.abs_nat x = S h).
 intro.
 case H3.
 rewrite H.
 exact O_S.

 cut (exists p : positive, (x + - (0))%Z = Zpos p).
 simpl in |- *.
 rewrite Zplus_0_r.
 intro.
 case H3.
 intros.
 rewrite H4.
 unfold Z.abs_nat in |- *.
 generalize x0.
 exact ZL4.
 apply Zcompare_Gt_spec.
 assumption.

 (***)
 cut ((x < 0)%Z \/ (0 < x)%Z).
 intro.
 apply
  or_ind with (A := (x < 0)%Z) (B := (0 < x)%Z) (P := (x < 0)%Z \/ (x > 0)%Z).
 intro.
 left.
 assumption.
 intro.
 right.
 apply Z.lt_gt.
 assumption.
 assumption.
 apply not_Zeq.
 assumption.
Qed.

Lemma absolu_2 : forall x : Z, x <> 0%Z -> Z.abs_nat x <> 0. (*QF*)
Proof.
 intros.
 intro.
 apply H.
 apply absolu_1.
 assumption.
Qed.




Lemma absolu_inject_nat : forall n : nat, Z.abs_nat (Z_of_nat n) = n.
Proof.
 simple induction n; simpl in |- *.
 reflexivity.
 intros.
 apply nat_of_P_o_P_of_succ_nat_eq_succ.
Qed.


Lemma eq_inj : forall m n : nat, m = n :>Z -> m = n.
Proof.
 intros.
 generalize (f_equal Z.abs_nat H).
 intro.
 rewrite (absolu_inject_nat m) in H0.
 rewrite (absolu_inject_nat n) in H0.
 assumption.
Qed.

Lemma lt_inj : forall m n : nat, (m < n)%Z -> m < n.
Proof.
 intros.
 omega.
Qed.

Lemma le_inj : forall m n : nat, (m <= n)%Z -> m <= n.
Proof.
 intros.
 omega.
Qed.


Lemma inject_nat_S_inf : forall x : Z, (0 < x)%Z -> {n : nat | x = S n}.
Proof.
 intros [| p| p] Hp; try discriminate Hp.
 exists (pred (nat_of_P p)).
 rewrite S_predn.
 symmetry  in |- *; apply ZL9.
 clear Hp;
  apply sym_not_equal; apply lt_O_neq; apply lt_O_nat_of_P.
Qed.



Lemma le_absolu :
 forall x y : Z,
 (0 <= x)%Z -> (0 <= y)%Z -> (x <= y)%Z -> Z.abs_nat x <= Z.abs_nat y.
Proof.
 intros [| x| x] [| y| y] Hx Hy Hxy;
  apply le_O_n ||
    (try
      match goal with
      | id1:(0 <= Zneg _)%Z |- _ =>
          apply False_ind; apply id1; constructor
      | id1:(Zpos _ <= 0)%Z |- _ =>
          apply False_ind; apply id1; constructor
      | id1:(Zpos _ <= Zneg _)%Z |- _ =>
          apply False_ind; apply id1; constructor
      end).
 simpl in |- *.
 apply le_inj.
 do 2 rewrite ZL9.
 assumption.
Qed.

Lemma lt_absolu :
 forall x y : Z,
 (0 <= x)%Z -> (0 <= y)%Z -> (x < y)%Z -> Z.abs_nat x < Z.abs_nat y.
Proof.
 intros [| x| x] [| y| y] Hx Hy Hxy; inversion Hxy;
  try
   match goal with
   | id1:(0 <= Zneg _)%Z |- _ =>
       apply False_ind; apply id1; constructor
   | id1:(Zpos _ <= 0)%Z |- _ =>
       apply False_ind; apply id1; constructor
   | id1:(Zpos _ <= Zneg _)%Z |- _ =>
       apply False_ind; apply id1; constructor
   end; simpl in |- *; apply lt_inj; repeat rewrite ZL9;
  assumption.
Qed.

Lemma absolu_plus :
 forall x y : Z,
 (0 <= x)%Z -> (0 <= y)%Z -> Z.abs_nat (x + y) = Z.abs_nat x + Z.abs_nat y.
Proof.
 intros [| x| x] [| y| y] Hx Hy; trivial;
  try
   match goal with
   | id1:(0 <= Zneg _)%Z |- _ =>
       apply False_ind; apply id1; constructor
   | id1:(Zpos _ <= 0)%Z |- _ =>
       apply False_ind; apply id1; constructor
   | id1:(Zpos _ <= Zneg _)%Z |- _ =>
       apply False_ind; apply id1; constructor
   end.
 rewrite <- BinInt.Zpos_plus_distr.
 unfold Z.abs_nat in |- *.
 apply nat_of_P_plus_morphism.
Qed.

Lemma pred_absolu :
 forall x : Z, (0 < x)%Z -> pred (Z.abs_nat x) = Z.abs_nat (x - 1).
Proof.
 intros x Hx.
 generalize (Z_lt_lt_S_eq_dec 0 x Hx); simpl in |- *; intros [H1| H1];
  [ replace (Z.abs_nat x) with (Z.abs_nat (x - 1 + 1));
     [ idtac | apply f_equal with Z; auto with zarith ];
     rewrite absolu_plus;
     [ unfold Z.abs_nat at 2, nat_of_P, Pos.iter_op in |- *; omega
     | auto with zarith
     | intro; discriminate ]
  | rewrite <- H1; reflexivity ].
Qed.

Definition pred_nat : forall (x : Z) (Hx : (0 < x)%Z), nat.
intros [| px| px] Hx; try abstract (discriminate Hx).
exact (pred (nat_of_P px)).
Defined.

Lemma pred_nat_equal :
 forall (x : Z) (Hx1 Hx2 : (0 < x)%Z), pred_nat x Hx1 = pred_nat x Hx2.
Proof.
 intros [| px| px] Hx1 Hx2; try (discriminate Hx1); trivial.
Qed.

Let pred_nat_unfolded_subproof px :
  Pos.to_nat px <> 0.
Proof.
apply sym_not_equal; apply lt_O_neq; apply lt_O_nat_of_P.
Qed.

Lemma pred_nat_unfolded :
 forall (x : Z) (Hx : (0 < x)%Z), x = S (pred_nat x Hx).
Proof.
 intros [| px| px] Hx; try discriminate Hx.
 unfold pred_nat in |- *.
 rewrite S_predn.
 symmetry  in |- *; apply ZL9.
 clear Hx; apply pred_nat_unfolded_subproof.
Qed.

Lemma absolu_pred_nat :
 forall (m : Z) (Hm : (0 < m)%Z), S (pred_nat m Hm) = Z.abs_nat m.
Proof.
 intros [| px| px] Hx; try discriminate Hx.
 unfold pred_nat in |- *.
 rewrite S_predn.
 reflexivity.
 apply pred_nat_unfolded_subproof.
Qed.

Lemma pred_nat_absolu :
 forall (m : Z) (Hm : (0 < m)%Z), pred_nat m Hm = Z.abs_nat (m - 1).
Proof.
 intros [| px| px] Hx; try discriminate Hx.
 unfold pred_nat in |- *.
 rewrite <- pred_absolu; reflexivity || assumption.
Qed.

Lemma minus_pred_nat :
 forall (n m : Z) (Hn : (0 < n)%Z) (Hm : (0 < m)%Z) (Hnm : (0 < n - m)%Z),
 S (pred_nat n Hn) - S (pred_nat m Hm) = S (pred_nat (n - m) Hnm).
Proof.
 intros.
 simpl in |- *.
 destruct n; try discriminate Hn.
 destruct m; try discriminate Hm.
 unfold pred_nat at 1 2 in |- *.
 rewrite minus_pred; try apply lt_O_nat_of_P.
 apply eq_inj.
 rewrite <- pred_nat_unfolded.
 rewrite Znat.inj_minus1.
 repeat rewrite ZL9.
 reflexivity.
 apply le_inj.
 apply Zlt_le_weak.
 repeat rewrite ZL9.
 apply Zlt_O_minus_lt.
 assumption.
Qed.


(*###########################################################################*)
(** Properties of Zsgn                                                       *)
(*###########################################################################*)


Lemma Zsgn_1 :
 forall x : Z, {Z.sgn x = 0%Z} + {Z.sgn x = 1%Z} + {Z.sgn x = (-1)%Z}. (*QF*)
Proof.
 intros.
 case x.
 left.
 left.
 unfold Z.sgn in |- *.
 reflexivity.
 intro.
 simpl in |- *.
 left.
 right.
 reflexivity.
 intro.
 right.
 simpl in |- *.
 reflexivity.
Qed.


Lemma Zsgn_2 : forall x : Z, Z.sgn x = 0%Z -> x = 0%Z.   (*QF*)
Proof.
 intros [| p1| p1]; simpl in |- *; intro H; constructor || discriminate H.
Qed.


Lemma Zsgn_3 : forall x : Z, x <> 0%Z -> Z.sgn x <> 0%Z.   (*QF*)
Proof.
 intro.
 case x.
 intros.
 apply False_ind.
 apply H.
 reflexivity.
 intros.
 simpl in |- *.
 discriminate.
 intros.
 simpl in |- *.
 discriminate.
Qed.




Theorem Zsgn_4 : forall a : Z, a = (Z.sgn a * Z.abs_nat a)%Z.  (*QF*)
Proof.
 intro.
 case a.
 simpl in |- *.
 reflexivity.
 intro.
 unfold Z.sgn in |- *.
 unfold Z.abs_nat in |- *.
 rewrite Zmult_1_l.
 symmetry  in |- *.
 apply ZL9.
 intros.
 unfold Z.sgn in |- *.
 unfold Z.abs_nat in |- *.
 rewrite ZL9.
 constructor.
Qed.


Theorem Zsgn_5 :
 forall a b x y : Z,
 x <> 0%Z ->
 y <> 0%Z ->
 (Z.sgn a * x)%Z = (Z.sgn b * y)%Z -> (Z.sgn a * y)%Z = (Z.sgn b * x)%Z.  (*QF*)
Proof.
 intros a b x y H H0.
 case a.

 case b.
 simpl in |- *.
 trivial.

 intro.
 unfold Z.sgn in |- *.
 intro.
 rewrite Zmult_1_l in H1.
 simpl in H1.
 apply False_ind.
 apply H0.
 symmetry  in |- *.
 assumption.
 intro.
 unfold Z.sgn in |- *.
 intro.
 apply False_ind.
 apply H0.
 apply Z.opp_inj.
 simpl in |- *.
 transitivity (-1 * y)%Z.
 constructor.
 transitivity (0 * x)%Z.
 symmetry  in |- *.
 assumption.
 simpl in |- *.
 reflexivity.
 intro.
 unfold Z.sgn at 1 in |- *.
 unfold Z.sgn at 2 in |- *.
 intro.
 transitivity y.
 rewrite Zmult_1_l.
 reflexivity.
 transitivity (Z.sgn b * (Z.sgn b * y))%Z.
 case (Zsgn_1 b).
 intro.
 case s.
 intro.
 apply False_ind.
 apply H.
 rewrite e in H1.
 change ((1 * x)%Z = 0%Z) in H1.
 rewrite Zmult_1_l in H1.
 assumption.
 intro.
 rewrite e.
 rewrite Zmult_1_l.
 rewrite Zmult_1_l.
 reflexivity.
 intro.
 rewrite e.
 ring.
 rewrite Zmult_1_l in H1.
 rewrite H1.
 reflexivity.
 intro.
 unfold Z.sgn at 1 in |- *.
 unfold Z.sgn at 2 in |- *.
 intro.
 transitivity (Z.sgn b * (-1 * (Z.sgn b * y)))%Z.
 case (Zsgn_1 b).
 intros.
 case s.
 intro.
 apply False_ind.
 apply H.
 apply Z.opp_inj.
 transitivity (-1 * x)%Z.
 ring.
 unfold Z.opp in |- *.
 rewrite e in H1.
 transitivity (0 * y)%Z.
 assumption.
 simpl in |- *.
 reflexivity.
 intro.
 rewrite e.
 ring.
 intro.
 rewrite e.
 ring.
 rewrite <- H1.
 ring.
Qed.

Lemma Zsgn_6 : forall x : Z, x = 0%Z -> Z.sgn x = 0%Z.
Proof.
 intros.
 rewrite H.
 simpl in |- *.
 reflexivity.
Qed.


Lemma Zsgn_7 : forall x : Z, (x > 0)%Z -> Z.sgn x = 1%Z.
Proof.
 intro.
 case x.
 intro.
 apply False_ind.
 apply (Z.lt_irrefl 0).
 Flip.
 intros.
 simpl in |- *.
 reflexivity.
 intros.
 apply False_ind.
 apply (Z.lt_irrefl (Zneg p)).
 apply Z.lt_trans with 0%Z.
 constructor.
 Flip.
Qed.


Lemma Zsgn_7' : forall x : Z, (0 < x)%Z -> Z.sgn x = 1%Z.
Proof.
 intros; apply Zsgn_7; Flip.
Qed.


Lemma Zsgn_8 : forall x : Z, (x < 0)%Z -> Z.sgn x = (-1)%Z.
Proof.
 intro.
 case x.
 intro.
 apply False_ind.
 apply (Z.lt_irrefl 0).
 assumption.
 intros.
 apply False_ind.
 apply (Z.lt_irrefl 0).
 apply Z.lt_trans with (Zpos p).
 constructor.
 assumption.
 intros.
 simpl in |- *.
 reflexivity.
Qed.

Lemma Zsgn_9 : forall x : Z, Z.sgn x = 1%Z -> (0 < x)%Z.
Proof.
 intro.
 case x.
 intro.
 apply False_ind.
 simpl in H.
 discriminate.
 intros.
 constructor.
 intros.
 apply False_ind.
 discriminate.
Qed.

Lemma Zsgn_10 : forall x : Z, Z.sgn x = (-1)%Z -> (x < 0)%Z.
Proof.
 intro.
 case x.
 intro.
 apply False_ind.
 discriminate.
 intros.
 apply False_ind.
 discriminate.
 intros.
 constructor.
Qed.

Lemma Zsgn_11 : forall x : Z, (Z.sgn x < 0)%Z -> (x < 0)%Z.
Proof.
 intros.
 apply Zsgn_10.
 case (Zsgn_1 x).
 intro.
 apply False_ind.
 case s.
 intro.
 generalize (Zorder.Zlt_not_eq _ _ H).
 intro.
 apply (H0 e).
 intro.
 rewrite e in H.
 generalize (Zorder.Zlt_not_eq _ _ H).
 intro.
 discriminate.
 trivial.
Qed.

Lemma Zsgn_12 : forall x : Z, (0 < Z.sgn x)%Z -> (0 < x)%Z.
Proof.
 intros.
 apply Zsgn_9.
 case (Zsgn_1 x).
 intro.
 case s.
 intro.
 generalize (Zorder.Zlt_not_eq _ _ H).
 intro.
 generalize (sym_eq e).
 intro.
 apply False_ind.
 apply (H0 H1).
 trivial.
 intro.
 rewrite e in H.
 generalize (Zorder.Zlt_not_eq _ _ H).
 intro.
 apply False_ind.
 discriminate.
Qed.

Lemma Zsgn_13 : forall x : Z, (0 <= Z.sgn x)%Z -> (0 <= x)%Z.
Proof.
 intros.
 case (Z_le_lt_eq_dec 0 (Z.sgn x) H).
 intro.
 apply Zlt_le_weak.
 apply Zsgn_12.
 assumption.
 intro.
 assert (x = 0%Z).
 apply Zsgn_2.
 symmetry  in |- *.
 assumption.
 rewrite H0.
 apply Z.le_refl.
Qed.

Lemma Zsgn_14 : forall x : Z, (Z.sgn x <= 0)%Z -> (x <= 0)%Z.
Proof.
 intros.
 case (Z_le_lt_eq_dec (Z.sgn x) 0 H).
 intro.
 apply Zlt_le_weak.
 apply Zsgn_11.
 assumption.
 intro.
 assert (x = 0%Z).
 apply Zsgn_2.
 assumption.
 rewrite H0.
 apply Z.le_refl.
Qed.

Lemma Zsgn_15 : forall x y : Z, Z.sgn (x * y) = (Z.sgn x * Z.sgn y)%Z.
Proof.
 intros [|p1|p1]; [intros y|intros [|p2|p2] ..]; simpl in |- *; constructor.
Qed.

Lemma Zsgn_16 :
 forall x y : Z,
 Z.sgn (x * y) = 1%Z -> {(0 < x)%Z /\ (0 < y)%Z} + {(x < 0)%Z /\ (y < 0)%Z}.
Proof.
 intros [|p1|p1]; [intros y|intros [|p2|p2] ..]; simpl in |- *; intro H;
  try discriminate H; [ left | right ]; repeat split.
Qed.

Lemma Zsgn_17 :
 forall x y : Z,
 Z.sgn (x * y) = (-1)%Z -> {(0 < x)%Z /\ (y < 0)%Z} + {(x < 0)%Z /\ (0 < y)%Z}.
Proof.
 intros [|p1|p1]; [intros y|intros [|p2|p2] ..]; simpl in |- *; intro H;
  try discriminate H; [ left | right ]; repeat split.
Qed.

Lemma Zsgn_18 : forall x y : Z, Z.sgn (x * y) = 0%Z -> {x = 0%Z} + {y = 0%Z}.
Proof.
 intros [|p1|p1]; [intros y|intros [|p2|p2] ..]; simpl in |- *; intro H;
  try discriminate H; [ left | right | right ]; constructor.
Qed.



Lemma Zsgn_19 : forall x y : Z, (0 < Z.sgn x + Z.sgn y)%Z -> (0 < x + y)%Z.
Proof.
 Proof.
 intros [|p1|p1]; [intros y|intros [|p2|p2] ..]; simpl in |- *; intro H;
  discriminate H || (constructor || apply Zsgn_12; assumption).
Qed.

Lemma Zsgn_20 : forall x y : Z, (Z.sgn x + Z.sgn y < 0)%Z -> (x + y < 0)%Z.
Proof.
 Proof.
 intros [|p1|p1]; [intros y|intros [|p2|p2] ..]; simpl in |- *; intro H;
  discriminate H || (constructor || apply Zsgn_11; assumption).
Qed.


Lemma Zsgn_21 : forall x y : Z, (0 < Z.sgn x + Z.sgn y)%Z -> (0 <= x)%Z.
Proof.
 intros [|p1|p1]; [intros y|intros [|p2|p2] ..]; simpl in |- *; intros H H0;
  discriminate H || discriminate H0.
Qed.

Lemma Zsgn_22 : forall x y : Z, (Z.sgn x + Z.sgn y < 0)%Z -> (x <= 0)%Z.
Proof.
 Proof.
 intros [|p1|p1]; [intros y|intros [|p2|p2] ..]; simpl in |- *; intros H H0;
  discriminate H || discriminate H0.
Qed.

Lemma Zsgn_23 : forall x y : Z, (0 < Z.sgn x + Z.sgn y)%Z -> (0 <= y)%Z.
Proof.
 intros [|p1|p1] [|p2|p2]; simpl in |- *;
  intros H H0; discriminate H || discriminate H0.
Qed.

Lemma Zsgn_24 : forall x y : Z, (Z.sgn x + Z.sgn y < 0)%Z -> (y <= 0)%Z.
Proof.
 intros [|p1|p1] [|p2|p2]; simpl in |- *;
  intros H H0; discriminate H || discriminate H0.
Qed.

Lemma Zsgn_25 : forall x : Z, Z.sgn (- x) = (- Z.sgn x)%Z.
Proof.
 intros [| p1| p1]; simpl in |- *; reflexivity.
Qed.


Lemma Zsgn_26 : forall x : Z, (0 < x)%Z -> (0 < Z.sgn x)%Z.
Proof.
 intros [| p| p] Hp; trivial.
Qed.

Lemma Zsgn_27 : forall x : Z, (x < 0)%Z -> (Z.sgn x < 0)%Z.
Proof.
 intros [| p| p] Hp; trivial.
Qed.

Hint Resolve Zsgn_1 Zsgn_2 Zsgn_3 Zsgn_4 Zsgn_5 Zsgn_6 Zsgn_7 Zsgn_7' Zsgn_8
  Zsgn_9 Zsgn_10 Zsgn_11 Zsgn_12 Zsgn_13 Zsgn_14 Zsgn_15 Zsgn_16 Zsgn_17
  Zsgn_18 Zsgn_19 Zsgn_20 Zsgn_21 Zsgn_22 Zsgn_23 Zsgn_24 Zsgn_25 Zsgn_26
  Zsgn_27: zarith.

(*###########################################################################*)
(** Properties of Zabs                                                       *)
(*###########################################################################*)

Lemma Zabs_1 : forall z p : Z, (Z.abs z < p)%Z -> (z < p)%Z /\ (- p < z)%Z.
Proof.
 intros z p.
 case z.
 intros.
 simpl in H.
 split.
 assumption.
 apply Zgt_mult_conv_absorb_l with (a := (-1)%Z).
 replace (-1)%Z with (Z.pred 0).
 apply Zlt_pred.
 simpl; trivial.
 ring_simplify (-1 * - p)%Z (-1 * 0)%Z.
 apply Z.lt_gt.
 assumption.

 intros.
 simpl in H.
 split.
 assumption.
 apply Z.lt_trans with (m := 0%Z).
 apply Zgt_mult_conv_absorb_l with (a := (-1)%Z).
 replace (-1)%Z with (Z.pred 0).
 apply Zlt_pred.
 simpl; trivial.
 ring_simplify (-1 * - p)%Z (-1 * 0)%Z.
 apply Z.lt_gt.
 apply Z.lt_trans with (m := Zpos p0).
 constructor.
 assumption.
 constructor.

 intros.
 simpl in H.
 split.
 apply Z.lt_trans with (m := Zpos p0).
 constructor.
 assumption.

 apply Zgt_mult_conv_absorb_l with (a := (-1)%Z).
 replace (-1)%Z with (Z.pred 0).
 apply Zlt_pred.
 simpl;trivial.
 ring_simplify (-1 * - p)%Z.
 replace (-1 * Zneg p0)%Z with (- Zneg p0)%Z.
 replace (- Zneg p0)%Z with (Zpos p0).
 apply Z.lt_gt.
 assumption.
 symmetry  in |- *.
 apply Zopp_neg.
 rewrite Zopp_mult_distr_l_reverse with (n := 1%Z).
 simpl in |- *.
 constructor.
Qed.


Lemma Zabs_2 : forall z p : Z, (Z.abs z > p)%Z -> (z > p)%Z \/ (- p > z)%Z.
Proof.
 intros z p.
 case z.
 intros.
 simpl in H.
 left.
 assumption.

 intros.
 simpl in H.
 left.
 assumption.

 intros.
 simpl in H.
 right.
 apply Z.lt_gt.
 apply Zgt_mult_conv_absorb_l with (a := (-1)%Z).
 constructor.
 ring_simplify (-1 * - p)%Z.
 replace (-1 * Zneg p0)%Z with (Zpos p0).
 assumption.
 reflexivity.
Qed.

Lemma Zabs_3 : forall z p : Z, (z < p)%Z /\ (- p < z)%Z -> (Z.abs z < p)%Z.
Proof.
 intros z p.
 case z.
  intro.
  simpl in |- *.
  elim H.
  intros.
  assumption.

  intros.
  elim H.
  intros.
  simpl in |- *.
  assumption.

  intros.
  elim H.
  intros.
  simpl in |- *.
  apply Zgt_mult_conv_absorb_l with (a := (-1)%Z).
  constructor.
  replace (-1 * Zpos p0)%Z with (Zneg p0).
  replace (-1 * p)%Z with (- p)%Z.
  apply Z.lt_gt.
  assumption.
  ring.
  simpl in |- *.
  reflexivity.
Qed.

Lemma Zabs_4 : forall z p : Z, (Z.abs z < p)%Z -> (- p < z < p)%Z.
Proof.
 intros.
 split.
 apply proj2 with (A := (z < p)%Z).
 apply Zabs_1.
 assumption.
 apply proj1 with (B := (- p < z)%Z).
 apply Zabs_1.
 assumption.
Qed.


Lemma Zabs_5 : forall z p : Z, (Z.abs z <= p)%Z -> (- p <= z <= p)%Z.
Proof.
 intros.
 split.
 replace (- p)%Z with (Z.succ (- Z.succ p)).
 apply Zlt_le_succ.
 apply proj2 with (A := (z < Z.succ p)%Z).
 apply Zabs_1.
 apply Zle_lt_succ.
 assumption.
 unfold Z.succ in |- *.
 ring.
 apply Zlt_succ_le.
 apply proj1 with (B := (- Z.succ p < z)%Z).
 apply Zabs_1.
 apply Zle_lt_succ.
 assumption.
Qed.

Lemma Zabs_6 : forall z p : Z, (Z.abs z <= p)%Z -> (z <= p)%Z.
Proof.
 intros.
 apply proj2 with (A := (- p <= z)%Z).
 apply Zabs_5.
 assumption.
Qed.

Lemma Zabs_7 : forall z p : Z, (Z.abs z <= p)%Z -> (- p <= z)%Z.
Proof.
 intros.
 apply proj1 with (B := (z <= p)%Z).
 apply Zabs_5.
 assumption.
Qed.

Lemma Zabs_8 : forall z p : Z, (- p <= z <= p)%Z -> (Z.abs z <= p)%Z.
Proof.
 intros.
 apply Zlt_succ_le.
 apply Zabs_3.
 elim H.
 intros.
 split.
 apply Zle_lt_succ.
 assumption.
 apply Z.lt_le_trans with (m := (- p)%Z).
 apply Z.gt_lt.
 apply Zlt_opp.
 apply Zlt_succ.
 assumption.
Qed.

Lemma Zabs_min : forall z : Z, Z.abs z = Z.abs (- z).
Proof.
 intro.
 case z.
 simpl in |- *.
 reflexivity.
 intro.
 simpl in |- *.
 reflexivity.
 intro.
 simpl in |- *.
 reflexivity.
Qed.

Lemma Zabs_9 :
 forall z p : Z, (0 <= p)%Z -> (p < z)%Z \/ (z < - p)%Z -> (p < Z.abs z)%Z.
Proof.
 intros.
 case H0.
 intro.
 replace (Z.abs z) with z.
 assumption.
 symmetry  in |- *.
 apply Z.abs_eq.
 apply Zlt_le_weak.
 apply Z.le_lt_trans with (m := p).
 assumption.
 assumption.
 intro.
 cut (Z.abs z = (- z)%Z).
 intro.
 rewrite H2.
 apply Zmin_cancel_Zlt.
 ring_simplify (- - z)%Z.
 assumption.
 rewrite Zabs_min.
 apply Z.abs_eq.
 apply Zlt_le_weak.
 apply Z.le_lt_trans with (m := p).
 assumption.
 apply Zmin_cancel_Zlt.
 ring_simplify (- - z)%Z.
 assumption.
Qed.

Lemma Zabs_10 : forall z : Z, (0 <= Z.abs z)%Z.
Proof.
 intro.
 case (Z_zerop z).
 intro.
 rewrite e.
 simpl in |- *.
 apply Z.le_refl.
 intro.
 case (not_Zeq z 0 n).
 intro.
 apply Zlt_le_weak.
 apply Zabs_9.
 apply Z.le_refl.
 simpl in |- *.
 right.
 assumption.
 intro.
 apply Zlt_le_weak.
 apply Zabs_9.
 apply Z.le_refl.
 simpl in |- *.
 left.
 assumption.
Qed.

Lemma Zabs_11 : forall z : Z, z <> 0%Z -> (0 < Z.abs z)%Z.
Proof.
 intros.
 apply Zabs_9.
 apply Z.le_refl.
 simpl in |- *.
 apply not_Zeq.
 intro.
 apply H.
 symmetry  in |- *.
 assumption.
Qed.

Lemma Zabs_12 : forall z m : Z, (m < Z.abs z)%Z -> {(m < z)%Z} + {(z < - m)%Z}.
Proof.
 intros [| p| p] m; simpl in |- *; intros H;
  [ left | left | right; apply Zmin_cancel_Zlt; rewrite Z.opp_involutive ];
  assumption.
Qed.

Lemma Zabs_mult : forall z p : Z, Z.abs (z * p) = (Z.abs z * Z.abs p)%Z.
Proof.
 intros.
 case z.
 simpl in |- *.
 reflexivity.
 case p.
 simpl in |- *.
 reflexivity.
 intros.
 simpl in |- *.
 reflexivity.
 intros.
 simpl in |- *.
 reflexivity.
 case p.
 intro.
 simpl in |- *.
 reflexivity.
 intros.
 simpl in |- *.
 reflexivity.
 intros.
 simpl in |- *.
 reflexivity.
Qed.

Lemma Zabs_plus : forall z p : Z, (Z.abs (z + p) <= Z.abs z + Z.abs p)%Z.
Proof.
 intros.
 case z.
 simpl in |- *.
 apply Z.le_refl.
 case p.
 intro.
 simpl in |- *.
 apply Z.le_refl.
 intros.
 simpl in |- *.
 apply Z.le_refl.
 intros.
 unfold Z.abs at 2 in |- *.
 unfold Z.abs at 2 in |- *.
 apply Zabs_8.
 split.
 apply Zplus_le_reg_l with (Zpos p1 - Zneg p0)%Z.
 replace (Zpos p1 - Zneg p0 + - (Zpos p1 + Zpos p0))%Z with
  (- (Zpos p0 + Zneg p0))%Z.
 replace (Zpos p1 - Zneg p0 + (Zpos p1 + Zneg p0))%Z with (2 * Zpos p1)%Z.
 replace (- (Zpos p0 + Zneg p0))%Z with 0%Z.
 apply Zmult_gt_0_le_0_compat.
 constructor.
 apply Zlt_le_weak.
 constructor.
 rewrite <- Zopp_neg with p0.
 ring.
 ring.
 ring.
 apply Zplus_le_compat.
 apply Z.le_refl.
 apply Zlt_le_weak.
 constructor.

 case p.
 simpl in |- *.
 intro.
 apply Z.le_refl.
 intros.
 unfold Z.abs at 2 in |- *.
 unfold Z.abs at 2 in |- *.
 apply Zabs_8.
 split.
 apply Zplus_le_reg_l with (Zpos p1 + Zneg p0)%Z.
 replace (Zpos p1 + Zneg p0 + - (Zpos p1 + Zpos p0))%Z with
  (Zneg p0 - Zpos p0)%Z.
 replace (Zpos p1 + Zneg p0 + (Zneg p1 + Zpos p0))%Z with 0%Z.
 apply Zplus_le_reg_l with (Zpos p0).
 replace (Zpos p0 + (Zneg p0 - Zpos p0))%Z with (Zneg p0).
 simpl in |- *.
 apply Zlt_le_weak.
 constructor.
 ring.
 replace (Zpos p1 + Zneg p0 + (Zneg p1 + Zpos p0))%Z with
  (Zpos p1 + Zneg p1 + (Zpos p0 + Zneg p0))%Z.
 replace 0%Z with (0 + 0)%Z.
 apply Zplus_eq_compat.
 rewrite <- Zopp_neg with p1.
 ring.
 rewrite <- Zopp_neg with p0.
 ring.
 simpl in |- *.
 constructor.
 ring.
 ring.
 apply Zplus_le_compat.
 apply Zlt_le_weak.
 constructor.
 apply Z.le_refl.
 intros.
 simpl in |- *.
 apply Z.le_refl.
Qed.

Lemma Zabs_neg : forall z : Z, (z <= 0)%Z -> Z.abs z = (- z)%Z.
Proof.
 intro.
 case z.
 simpl in |- *.
 intro.
 reflexivity.
 intros.
 apply False_ind.
 apply H.
 simpl in |- *.
 reflexivity.
 intros.
 simpl in |- *.
 reflexivity.
Qed.

Lemma Zle_Zabs: forall z, (z <= Z.abs z)%Z.
Proof.
 intros [|z|z]; simpl; auto with zarith; apply Zle_neg_pos.
Qed.

Hint Resolve Zabs_1 Zabs_2 Zabs_3 Zabs_4 Zabs_5 Zabs_6 Zabs_7 Zabs_8 Zabs_9
  Zabs_10 Zabs_11 Zabs_12 Zabs_min Zabs_neg Zabs_mult Zabs_plus Zle_Zabs: zarith.


(*###########################################################################*)
(** Induction on Z                                                           *)
(*###########################################################################*)

Lemma Zind :
 forall (P : Z -> Prop) (p : Z),
 P p ->
 (forall q : Z, (p <= q)%Z -> P q -> P (q + 1)%Z) ->
 forall q : Z, (p <= q)%Z -> P q.
Proof.
 intros P p.
 intro.
 intro.
 cut (forall q : Z, (p <= q)%Z -> exists k : nat, q = (p + k)%Z).
 intro.
 cut (forall k : nat, P (p + k)%Z).
 intro.
 intros.
 cut (exists k : nat, q = (p + Z_of_nat k)%Z).
 intro.
 case H4.
 intros.
 rewrite H5.
 apply H2.
 apply H1.
 assumption.
 intro.
 induction  k as [| k Hreck].
 simpl in |- *.
 ring_simplify (p + 0)%Z.
 assumption.
 replace (p + Z_of_nat (S k))%Z with (p + k + 1)%Z.
 apply H0.
 apply Zplus_le_reg_l with (p := (- p)%Z).
 replace (- p + p)%Z with (Z_of_nat 0).
 ring_simplify (- p + (p + Z_of_nat k))%Z.
 apply Znat.inj_le.
 apply le_O_n.
 ring_simplify; auto with arith.
 assumption.
 rewrite (Znat.inj_S k).
 unfold Z.succ in |- *.
 ring.
 intros.
 cut (exists k : nat, (q - p)%Z = Z_of_nat k).
 intro.
 case H2.
 intro k.
 intros.
 exists k.
 apply Zplus_reg_l with (n := (- p)%Z).
 replace (- p + q)%Z with (q - p)%Z.
 rewrite H3.
 ring.
 ring.
 apply Z_of_nat_complete.
 unfold Zminus in |- *.
 apply Zle_left.
 assumption.
Qed.

Lemma Zrec :
 forall (P : Z -> Set) (p : Z),
 P p ->
 (forall q : Z, (p <= q)%Z -> P q -> P (q + 1)%Z) ->
 forall q : Z, (p <= q)%Z -> P q.
Proof.
 intros F p.
 intro.
 intro.
 cut (forall q : Z, (p <= q)%Z -> {k : nat | q = (p + k)%Z}).
 intro.
 cut (forall k : nat, F (p + k)%Z).
 intro.
 intros.
 cut {k : nat | q = (p + Z_of_nat k)%Z}.
 intro.
 case H4.
 intros.
 rewrite e.
 apply H2.
 apply H1.
 assumption.
 intro.
 induction  k as [| k Hreck].
 simpl in |- *.
 rewrite Zplus_0_r.
 assumption.
 replace (p + Z_of_nat (S k))%Z with (p + k + 1)%Z.
 apply H0.
 apply Zplus_le_reg_l with (p := (- p)%Z).
 replace (- p + p)%Z with (Z_of_nat 0).
 replace (- p + (p + Z_of_nat k))%Z with (Z_of_nat k).
 apply Znat.inj_le.
 apply le_O_n.
 rewrite Zplus_assoc; rewrite Zplus_opp_l; reflexivity.
 rewrite Zplus_opp_l; reflexivity.
 assumption.
 rewrite (Znat.inj_S k).
 unfold Z.succ in |- *.
 apply Zplus_assoc_reverse.
 intros.
 cut {k : nat | (q - p)%Z = Z_of_nat k}.
 intro H2.
 case H2.
 intro k.
 intros.
 exists k.
 apply Zplus_reg_l with (n := (- p)%Z).
 replace (- p + q)%Z with (q - p)%Z.
 rewrite e.
 rewrite Zplus_assoc; rewrite Zplus_opp_l; reflexivity.
 unfold Zminus in |- *.
 apply Zplus_comm.
 apply Z_of_nat_complete_inf.
 unfold Zminus in |- *.
 apply Zle_left.
 assumption.
Qed.

Lemma Zrec_down :
 forall (P : Z -> Set) (p : Z),
 P p ->
 (forall q : Z, (q <= p)%Z -> P q -> P (q - 1)%Z) ->
 forall q : Z, (q <= p)%Z -> P q.
Proof.
 intros F p.
 intro.
 intro.
 cut (forall q : Z, (q <= p)%Z -> {k : nat | q = (p - k)%Z}).
 intro.
 cut (forall k : nat, F (p - k)%Z).
 intro.
 intros.
 cut {k : nat | q = (p - Z_of_nat k)%Z}.
 intro.
 case H4.
 intros.
 rewrite e.
 apply H2.
 apply H1.
 assumption.
 intro.
 induction  k as [| k Hreck].
 simpl in |- *.
 replace (p - 0)%Z with p.
 assumption.
 unfold Zminus in |- *.
 unfold Z.opp in |- *.
 rewrite Zplus_0_r; reflexivity.
 replace (p - Z_of_nat (S k))%Z with (p - k - 1)%Z.
 apply H0.
 apply Zplus_le_reg_l with (p := (- p)%Z).
 replace (- p + p)%Z with (- Z_of_nat 0)%Z.
 replace (- p + (p - Z_of_nat k))%Z with (- Z_of_nat k)%Z.
 apply Z.ge_le.
 apply Zge_opp.
 apply Znat.inj_le.
 apply le_O_n.
 unfold Zminus in |- *; rewrite Zplus_assoc; rewrite Zplus_opp_l; reflexivity.
 rewrite Zplus_opp_l; reflexivity.
 assumption.
 rewrite (Znat.inj_S k).
 unfold Z.succ in |- *.
 unfold Zminus at 1 2 in |- *.
 rewrite Zplus_assoc_reverse.
 rewrite <- Zopp_plus_distr.
 reflexivity.
 intros.
 cut {k : nat | (p - q)%Z = Z_of_nat k}.
 intro.
 case H2.
 intro k.
 intros.
 exists k.
 apply Z.opp_inj.
 apply Zplus_reg_l with (n := p).
 replace (p + - (p - Z_of_nat k))%Z with (Z_of_nat k).
 rewrite <- e.
 reflexivity.
 unfold Zminus in |- *.
 rewrite Zopp_plus_distr.
 rewrite Zplus_assoc.
 rewrite Zplus_opp_r.
 rewrite Z.opp_involutive.
 reflexivity.
 apply Z_of_nat_complete_inf.
 unfold Zminus in |- *.
 apply Zle_left.
 assumption.
Qed.

Lemma Zind_down :
 forall (P : Z -> Prop) (p : Z),
 P p ->
 (forall q : Z, (q <= p)%Z -> P q -> P (q - 1)%Z) ->
 forall q : Z, (q <= p)%Z -> P q.
Proof.
 intros F p.
 intro.
 intro.
 cut (forall q : Z, (q <= p)%Z -> exists k : nat, q = (p - k)%Z).
 intro.
 cut (forall k : nat, F (p - k)%Z).
 intro.
 intros.
 cut (exists k : nat, q = (p - Z_of_nat k)%Z).
 intro.
 case H4.
 intros x e.
 rewrite e.
 apply H2.
 apply H1.
 assumption.
 intro.
 induction  k as [| k Hreck].
 simpl in |- *.
 replace (p - 0)%Z with p.
 assumption.
 ring.
 replace (p - Z_of_nat (S k))%Z with (p - k - 1)%Z.
 apply H0.
 apply Zplus_le_reg_l with (p := (- p)%Z).
 replace (- p + p)%Z with (- Z_of_nat 0)%Z.
 replace (- p + (p - Z_of_nat k))%Z with (- Z_of_nat k)%Z.
 apply Z.ge_le.
 apply Zge_opp.
 apply Znat.inj_le.
 apply le_O_n.
 ring.
 ring_simplify; auto with arith.
 assumption.
 rewrite (Znat.inj_S k).
 unfold Z.succ in |- *.
 ring.
 intros.
 cut (exists k : nat, (p - q)%Z = Z_of_nat k).
 intro.
 case H2.
 intro k.
 intros.
 exists k.
 apply Z.opp_inj.
 apply Zplus_reg_l with (n := p).
 replace (p + - (p - Z_of_nat k))%Z with (Z_of_nat k).
 rewrite <- H3.
 ring.
 ring.
 apply Z_of_nat_complete.
 unfold Zminus in |- *.
 apply Zle_left.
 assumption.
Qed.

Lemma Zrec_wf :
 forall (P : Z -> Set) (p : Z),
 (forall q : Z, (forall r : Z, (p <= r < q)%Z -> P r) -> P q) ->
 forall q : Z, (p <= q)%Z -> P q.
Proof.
 intros P p WF_ind_step q Hq.
 cut (forall x : Z, (p <= x)%Z -> forall y : Z, (p <= y < x)%Z -> P y).
 intro.
 apply (H (Z.succ q)).
 apply Zle_le_succ.
 assumption.

 split; [ assumption | exact (Zlt_succ q) ].

 intros x0 Hx0; generalize Hx0; pattern x0 in |- *.
 apply Zrec with (p := p).
 intros.
 absurd (p <= p)%Z.
 apply Zgt_not_le.
 apply Zgt_le_trans with (m := y).
 apply Z.lt_gt.
 elim H.
 intros.
 assumption.
 elim H.
 intros.
 assumption.
 apply Z.le_refl.

 intros.
 apply WF_ind_step.
 intros.
 apply (H0 H).
 split.
 elim H2.
 intros.
 assumption.
 apply Z.lt_le_trans with y.
 elim H2.
 intros.
 assumption.
 apply Zgt_succ_le.
 apply Z.lt_gt.
 elim H1.
 intros.
 unfold Z.succ in |- *.
 assumption.
 assumption.
Qed.

Lemma Zrec_wf2 :
 forall (q : Z) (P : Z -> Set) (p : Z),
 (forall q : Z, (forall r : Z, (p <= r < q)%Z -> P r) -> P q) ->
 (p <= q)%Z -> P q.
Proof.
 intros.
 apply Zrec_wf with (p := p).
 assumption.
 assumption.
Qed.

Lemma Zrec_wf_double :
 forall (P : Z -> Z -> Set) (p0 q0 : Z),
 (forall n m : Z,
  (forall p q : Z, (q0 <= q)%Z -> (p0 <= p < n)%Z -> P p q) ->
  (forall p : Z, (q0 <= p < m)%Z -> P n p) -> P n m) ->
 forall p q : Z, (q0 <= q)%Z -> (p0 <= p)%Z -> P p q.
Proof.
 intros P p0 q0 Hrec p.
 intros.
 generalize q H.
 pattern p in |- *.
 apply Zrec_wf with (p := p0).
 intros p1 H1.
 intros.
 pattern q1 in |- *.
 apply Zrec_wf with (p := q0).
 intros q2 H3.
 apply Hrec.
 intros.
 apply H1.
 assumption.
 assumption.
 intros.
 apply H3.
 assumption.
 assumption.
 assumption.
Qed.

Lemma Zind_wf :
 forall (P : Z -> Prop) (p : Z),
 (forall q : Z, (forall r : Z, (p <= r < q)%Z -> P r) -> P q) ->
 forall q : Z, (p <= q)%Z -> P q.
Proof.
 intros P p WF_ind_step q Hq.
 cut (forall x : Z, (p <= x)%Z -> forall y : Z, (p <= y < x)%Z -> P y).
 intro.
 apply (H (Z.succ q)).
 apply Zle_le_succ.
 assumption.

 split; [ assumption | exact (Zlt_succ q) ].

 intros x0 Hx0; generalize Hx0; pattern x0 in |- *.
 apply Zind with (p := p).
 intros.
 absurd (p <= p)%Z.
 apply Zgt_not_le.
 apply Zgt_le_trans with (m := y).
 apply Z.lt_gt.
 elim H.
 intros.
 assumption.
 elim H.
 intros.
 assumption.
 apply Z.le_refl.

 intros.
 apply WF_ind_step.
 intros.
 apply (H0 H).
 split.
 elim H2.
 intros.
 assumption.
 apply Z.lt_le_trans with y.
 elim H2.
 intros.
 assumption.
 apply Zgt_succ_le.
 apply Z.lt_gt.
 elim H1.
 intros.
 unfold Z.succ in |- *.
 assumption.
 assumption.
Qed.

Lemma Zind_wf2 :
 forall (q : Z) (P : Z -> Prop) (p : Z),
 (forall q : Z, (forall r : Z, (p <= r < q)%Z -> P r) -> P q) ->
 (p <= q)%Z -> P q.
Proof.
 intros.
 apply Zind_wf with (p := p).
 assumption.
 assumption.
Qed.

Lemma Zind_wf_double :
 forall (P : Z -> Z -> Prop) (p0 q0 : Z),
 (forall n m : Z,
  (forall p q : Z, (q0 <= q)%Z -> (p0 <= p < n)%Z -> P p q) ->
  (forall p : Z, (q0 <= p < m)%Z -> P n p) -> P n m) ->
 forall p q : Z, (q0 <= q)%Z -> (p0 <= p)%Z -> P p q.
Proof.
 intros P p0 q0 Hrec p.
 intros.
 generalize q H.
 pattern p in |- *.
 apply Zind_wf with (p := p0).
 intros p1 H1.
 intros.
 pattern q1 in |- *.
 apply Zind_wf with (p := q0).
 intros q2 H3.
 apply Hrec.
 intros.
 apply H1.
 assumption.
 assumption.
 intros.
 apply H3.
 assumption.
 assumption.
 assumption.
Qed.

(*###########################################################################*)
(** Properties of Zmax                                                       *)
(*###########################################################################*)

Definition Zmax (n m : Z) := (n + m - Z.min n m)%Z.

Lemma ZmaxSS : forall n m : Z, (Zmax n m + 1)%Z = Zmax (n + 1) (m + 1).
Proof.
 intros.
 unfold Zmax in |- *.
 replace (Z.min (n + 1) (m + 1)) with (Z.min n m + 1)%Z.
 ring.
 symmetry  in |- *.
 change (Z.min (Z.succ n) (Z.succ m) = Z.succ (Z.min n m)) in |- *.
 symmetry  in |- *.
 apply Zmin_SS.
Qed.

Lemma Zle_max_l : forall n m : Z, (n <= Zmax n m)%Z.
Proof.
 intros.
 unfold Zmax in |- *.
 apply Zplus_le_reg_l with (p := (- n + Z.min n m)%Z).
 ring_simplify (- n + Z.min n m + n)%Z.
 ring_simplify (- n + Z.min n m + (n + m - Z.min n m))%Z.
 apply Z.le_min_r.
Qed.

Lemma Zle_max_r : forall n m : Z, (m <= Zmax n m)%Z.
Proof.
 intros.
 unfold Zmax in |- *.
 apply Zplus_le_reg_l with (p := (- m + Z.min n m)%Z).
 ring_simplify (- m + Z.min n m + m)%Z.
 ring_simplify (- m + Z.min n m + (n + m - Z.min n m))%Z.
 apply Z.le_min_l.
Qed.


Lemma Zmin_or_informative : forall n m : Z, {Z.min n m = n} + {Z.min n m = m}.
Proof.
 intros.
 case (Z_lt_ge_dec n m).
 unfold Z.min in |- *.
 unfold Z.lt in |- *.
 intro z.
 rewrite z.
 left.
 reflexivity.
 intro.
 cut ({(n > m)%Z} + {n = m :>Z}).
 intro.
 case H.
 intros z0.
 unfold Z.min in |- *.
 unfold Z.gt in z0.
 rewrite z0.
 right.
 reflexivity.
 intro.
 rewrite e.
 right.
 apply Zmin_n_n.
 cut ({(m < n)%Z} + {m = n :>Z}).
 intro.
 elim H.
 intro.
 left.
 apply Z.lt_gt.
 assumption.
 intro.
 right.
 symmetry  in |- *.
 assumption.
 apply Z_le_lt_eq_dec.
 apply Z.ge_le.
 assumption.
Qed.

Lemma Zmax_case : forall (n m : Z) (P : Z -> Set), P n -> P m -> P (Zmax n m).
Proof.
 intros.
 unfold Zmax in |- *.
 case Zmin_or_informative with (n := n) (m := m).
 intro.
 rewrite e.
 cut ((n + m - n)%Z = m).
 intro.
 rewrite H1.
 assumption.
 ring.
 intro.
 rewrite e.
 cut ((n + m - m)%Z = n).
 intro.
 rewrite H1.
 assumption.
 ring.
Qed.

Lemma Zmax_or_informative : forall n m : Z, {Zmax n m = n} + {Zmax n m = m}.
Proof.
 intros.
 unfold Zmax in |- *.
 case Zmin_or_informative with (n := n) (m := m).
 intro.
 rewrite e.
 right.
 ring.
 intro.
 rewrite e.
 left.
 ring.
Qed.

Lemma Zmax_n_n : forall n : Z, Zmax n n = n.
Proof.
 intros.
 unfold Zmax in |- *.
 rewrite (Zmin_n_n n).
 ring.
Qed.

Hint Resolve ZmaxSS Zle_max_r Zle_max_l Zmax_n_n: zarith.

(*###########################################################################*)
(** Properties of Arity                                                      *)
(*###########################################################################*)

Lemma Zeven_S : forall x : Z, Zeven.Zodd x -> Zeven.Zeven (x + 1).
Proof.
 exact Zeven.Zeven_Sn.
Qed.

Lemma Zeven_pred : forall x : Z, Zeven.Zodd x -> Zeven.Zeven (x - 1).
Proof.
 exact Zeven.Zeven_pred.
Qed.

(* This lemma used to be useful since it was mentioned with an unnecessary premise
   `x>=0` as Z_modulo_2 in ZArith, but the ZArith version has been fixed. *)

Definition Z_modulo_2_always :
  forall x : Z, {y : Z | x = (2 * y)%Z} + {y : Z | x = (2 * y + 1)%Z} :=
  Zeven.Z_modulo_2.

(*###########################################################################*)
(** Properties of Zdiv                                                       *)
(*###########################################################################*)

Lemma Z_div_mod_eq_2 :
 forall a b : Z, (0 < b)%Z -> (b * (a / b))%Z = (a - a mod b)%Z.
Proof.
 intros.
 apply Zplus_minus_eq.
 rewrite Zplus_comm.
 apply Z_div_mod_eq.
 Flip.
Qed.

Lemma Z_div_le :
 forall a b c : Z, (0 < c)%Z -> (b <= a)%Z -> (b / c <= a / c)%Z.
Proof.
 intros.
 apply Z.ge_le.
 apply Z_div_ge; Flip; assumption.
Qed.

Lemma Z_div_nonneg :
 forall a b : Z, (0 < b)%Z -> (0 <= a)%Z -> (0 <= a / b)%Z.
Proof.
 intros.
 apply Z.ge_le.
 apply Z_div_ge0; Flip; assumption.
Qed.

Lemma Z_div_neg : forall a b : Z, (0 < b)%Z -> (a < 0)%Z -> (a / b < 0)%Z.
Proof.
 intros.
 rewrite (Z_div_mod_eq a b) in H0.
 elim (Z_mod_lt a b).
 intros H1 _.
 apply Znot_ge_lt.
 intro.
 apply (Zlt_not_le (b * (a / b) + a mod b) 0 H0).
 apply Zplus_le_0_compat.
 apply Zmult_le_0_compat.
 apply Zlt_le_weak; assumption.
 Flip.
 assumption.
 Flip.
 Flip.
Qed.

Hint Resolve Z_div_mod_eq_2 Z_div_le Z_div_nonneg Z_div_neg: zarith.

(*###########################################################################*)
(** Properties of Zpower                                                       *)
(*###########################################################################*)

Lemma Zpower_1 : forall a : Z, (a ^ 1)%Z = a.
Proof.
 intros; unfold Zpower in |- *; unfold Zpower_pos in |- *; simpl in |- *;
  auto with zarith.
Qed.

Lemma Zpower_2 : forall a : Z, (a ^ 2)%Z = (a * a)%Z.
Proof.
 intros; unfold Zpower in |- *; unfold Zpower_pos in |- *; simpl in |- *;
  ring.
Qed.

Hint Resolve Zpower_1 Zpower_2: zarith.
