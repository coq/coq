(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

(** * NMake *)

(** From a cyclic Z/nZ representation to arbitrary precision natural numbers.*)

(** NB: This file contain the part which is independent from the underlying
    representation. The representation-dependent (and macro-generated) part
    is now in [NMake_gen]. *)

Require Import BigNumPrelude ZArith CyclicAxioms.
Require Import Nbasic Wf_nat StreamMemo NSig NMake_gen.

Module Make (Import W0:CyclicType) <: NType.

 (** Macro-generated part *)

 Include NMake_gen.Make W0.


 (** * Predecessor *)

 Lemma spec_pred : forall x, [pred x] = Zmax 0 ([x]-1).
 Proof.
 intros. destruct (Zle_lt_or_eq _ _ (spec_pos x)).
 rewrite Zmax_r; auto with zarith.
 apply spec_pred_pos; auto.
 rewrite <- H; apply spec_pred0; auto.
 Qed.


 (** * Subtraction *)

 Lemma spec_sub : forall x y, [sub x y] = Zmax 0 ([x]-[y]).
 Proof.
 intros. destruct (Zle_or_lt [y] [x]).
 rewrite Zmax_r; auto with zarith. apply spec_sub_pos; auto.
 rewrite Zmax_l; auto with zarith. apply spec_sub0; auto.
 Qed.

 (** * Comparison *)

 Theorem spec_compare : forall x y, compare x y = Zcompare [x] [y].
 Proof.
 intros x y. generalize (spec_compare_aux x y); destruct compare;
 intros; symmetry; try rewrite Zcompare_Eq_iff_eq; assumption.
 Qed.

 Definition eq_bool x y :=
  match compare x y with
  | Eq => true
  | _  => false
  end.

 Theorem spec_eq_bool : forall x y, eq_bool x y = Zeq_bool [x] [y].
 Proof.
 intros. unfold eq_bool, Zeq_bool. rewrite spec_compare; reflexivity.
 Qed.

 Theorem spec_eq_bool_aux: forall x y,
    if eq_bool x y then [x] = [y] else [x] <> [y].
 Proof.
 intros x y; unfold eq_bool.
 generalize (spec_compare_aux x y); case compare; auto with zarith.
 Qed.

 Definition lt n m := [n] < [m].
 Definition le n m := [n] <= [m].

 Definition min n m := match compare n m with Gt => m | _ => n end.
 Definition max n m := match compare n m with Lt => m | _ => n end.

 Theorem spec_max : forall n m, [max n m] = Zmax [n] [m].
 Proof.
 intros. unfold max, Zmax. rewrite spec_compare; destruct Zcompare; reflexivity.
 Qed.

 Theorem spec_min : forall n m, [min n m] = Zmin [n] [m].
 Proof.
 intros. unfold min, Zmin. rewrite spec_compare; destruct Zcompare; reflexivity.
 Qed.


 (** * Power *)

 Fixpoint power_pos (x:t) (p:positive) {struct p} : t :=
  match p with
  | xH => x
  | xO p => square (power_pos x p)
  | xI p => mul (square (power_pos x p)) x
  end.

 Theorem spec_power_pos: forall x n, [power_pos x n] = [x] ^ Zpos n.
 Proof.
 intros x n; generalize x; elim n; clear n x; simpl power_pos.
 intros; rewrite spec_mul; rewrite spec_square; rewrite H.
 rewrite Zpos_xI; rewrite Zpower_exp; auto with zarith.
 rewrite (Zmult_comm 2); rewrite Zpower_mult; auto with zarith.
 rewrite Zpower_2; rewrite Zpower_1_r; auto.
 intros; rewrite spec_square; rewrite H.
 rewrite Zpos_xO; auto with zarith.
 rewrite (Zmult_comm 2); rewrite Zpower_mult; auto with zarith.
 rewrite Zpower_2; auto.
 intros; rewrite Zpower_1_r; auto.
 Qed.

 Definition power x (n:N) := match n with
  | BinNat.N0 => one
  | BinNat.Npos p => power_pos x p
 end.

 Theorem spec_power: forall x n, [power x n] = [x] ^ Z_of_N n.
 Proof.
 destruct n; simpl. apply (spec_1 w0_spec).
 apply spec_power_pos.
 Qed.


 (** * Div *)

 Definition div_eucl x y :=
  if eq_bool y zero then (zero,zero) else
  match compare x y with
  | Eq => (one, zero)
  | Lt => (zero, x)
  | Gt => div_gt x y
  end.

 Theorem spec_div_eucl: forall x y,
      let (q,r) := div_eucl x y in
      ([q], [r]) = Zdiv_eucl [x] [y].
 Proof.
 assert (F0: [zero] = 0).
   exact (spec_0 w0_spec).
 assert (F1: [one] = 1).
   exact (spec_1 w0_spec).
 intros x y. unfold div_eucl.
 generalize (spec_eq_bool_aux y zero). destruct eq_bool; rewrite F0.
 intro H. rewrite H. destruct [x]; auto.
 intro H'.
 assert (0 < [y]) by (generalize (spec_pos y); auto with zarith).
 clear H'.
 generalize (spec_compare_aux x y); case compare; try rewrite F0;
   try rewrite F1; intros; auto with zarith.
 rewrite H0; generalize (Z_div_same [y] (Zlt_gt _ _ H))
                        (Z_mod_same [y] (Zlt_gt _ _ H));
  unfold Zdiv, Zmod; case Zdiv_eucl; intros; subst; auto.
 assert (F2: 0 <= [x] < [y]).
   generalize (spec_pos x); auto.
 generalize (Zdiv_small _ _ F2)
            (Zmod_small _ _ F2);
  unfold Zdiv, Zmod; case Zdiv_eucl; intros; subst; auto.
 generalize (spec_div_gt _ _ H0 H); auto.
 unfold Zdiv, Zmod; case Zdiv_eucl; case div_gt.
 intros a b c d (H1, H2); subst; auto.
 Qed.

 Definition div x y := fst (div_eucl x y).

 Theorem spec_div:
   forall x y, [div x y] = [x] / [y].
 Proof.
 intros x y; unfold div; generalize (spec_div_eucl x y);
   case div_eucl; simpl fst.
 intros xx yy; unfold Zdiv; case Zdiv_eucl; intros qq rr H;
  injection H; auto.
 Qed.


 (** * Modulo *)

 Definition modulo x y :=
  if eq_bool y zero then zero else
  match compare x y with
  | Eq => zero
  | Lt => x
  | Gt => mod_gt x y
  end.

 Theorem spec_modulo:
   forall x y, [modulo x y] = [x] mod [y].
 Proof.
 assert (F0: [zero] = 0).
   exact (spec_0 w0_spec).
 assert (F1: [one] = 1).
   exact (spec_1 w0_spec).
 intros x y. unfold modulo.
 generalize (spec_eq_bool_aux y zero). destruct eq_bool; rewrite F0.
 intro H; rewrite H. destruct [x]; auto.
 intro H'.
 assert (H : 0 < [y]) by (generalize (spec_pos y); auto with zarith).
 clear H'.
 generalize (spec_compare_aux x y); case compare; try rewrite F0;
   try rewrite F1; intros; try split; auto with zarith.
 rewrite H0; apply sym_equal; apply Z_mod_same; auto with zarith.
 apply sym_equal; apply Zmod_small; auto with zarith.
 generalize (spec_pos x); auto with zarith.
 apply spec_mod_gt; auto.
 Qed.


 (** * Gcd *)

 Definition gcd_gt_body a b cont :=
  match compare b zero with
  | Gt =>
    let r := mod_gt a b in
    match compare r zero with
    | Gt => cont r (mod_gt b r)
    | _ => b
    end
  | _ => a
  end.

 Theorem Zspec_gcd_gt_body: forall a b cont p,
    [a] > [b] -> [a] < 2 ^ p ->
      (forall a1 b1, [a1] < 2 ^ (p - 1) -> [a1] > [b1] ->
         Zis_gcd  [a1] [b1] [cont a1 b1]) ->
      Zis_gcd [a] [b] [gcd_gt_body a b cont].
 Proof.
 assert (F1: [zero] = 0).
   unfold zero, w_0, to_Z; rewrite (spec_0 w0_spec); auto.
 intros a b cont p H2 H3 H4; unfold gcd_gt_body.
 generalize (spec_compare_aux b zero); case compare; try rewrite F1.
   intros HH; rewrite HH; apply Zis_gcd_0.
 intros HH; absurd (0 <= [b]); auto with zarith.
 case (spec_digits b); auto with zarith.
 intros H5; generalize (spec_compare_aux (mod_gt a b) zero);
   case compare; try rewrite F1.
 intros H6; rewrite <- (Zmult_1_r [b]).
 rewrite (Z_div_mod_eq [a] [b]); auto with zarith.
 rewrite <- spec_mod_gt; auto with zarith.
 rewrite H6; rewrite Zplus_0_r.
 apply Zis_gcd_mult; apply Zis_gcd_1.
 intros; apply False_ind.
 case (spec_digits (mod_gt a b)); auto with zarith.
 intros H6; apply DoubleDiv.Zis_gcd_mod; auto with zarith.
 apply DoubleDiv.Zis_gcd_mod; auto with zarith.
 rewrite <- spec_mod_gt; auto with zarith.
 assert (F2: [b] > [mod_gt a b]).
   case (Z_mod_lt [a] [b]); auto with zarith.
   repeat rewrite <- spec_mod_gt; auto with zarith.
 assert (F3: [mod_gt a b] > [mod_gt b  (mod_gt a b)]).
   case (Z_mod_lt [b] [mod_gt a b]); auto with zarith.
   rewrite <- spec_mod_gt; auto with zarith.
 repeat rewrite <- spec_mod_gt; auto with zarith.
 apply H4; auto with zarith.
 apply Zmult_lt_reg_r with 2; auto with zarith.
 apply Zle_lt_trans with ([b] + [mod_gt a b]); auto with zarith.
 apply Zle_lt_trans with (([a]/[b]) * [b] + [mod_gt a b]); auto with zarith.
   apply Zplus_le_compat_r.
 pattern [b] at 1; rewrite <- (Zmult_1_l [b]).
 apply Zmult_le_compat_r; auto with zarith.
 case (Zle_lt_or_eq 0 ([a]/[b])); auto with zarith.
 intros HH; rewrite (Z_div_mod_eq [a] [b]) in H2;
   try rewrite <- HH in H2; auto with zarith.
 case (Z_mod_lt [a] [b]); auto with zarith.
 rewrite Zmult_comm; rewrite spec_mod_gt; auto with zarith.
 rewrite <- Z_div_mod_eq; auto with zarith.
 pattern 2 at 2; rewrite <- (Zpower_1_r 2).
 rewrite <- Zpower_exp; auto with zarith.
 ring_simplify (p - 1 + 1); auto.
 case (Zle_lt_or_eq 0 p); auto with zarith.
 generalize H3; case p; simpl Zpower; auto with zarith.
 intros HH; generalize H3; rewrite <- HH; simpl Zpower; auto with zarith.
 Qed.

 Fixpoint gcd_gt_aux (p:positive) (cont:t->t->t) (a b:t) {struct p} : t :=
  gcd_gt_body a b
    (fun a b =>
       match p with
       | xH => cont a b
       | xO p => gcd_gt_aux p (gcd_gt_aux p cont) a b
       | xI p => gcd_gt_aux p (gcd_gt_aux p cont) a b
       end).

 Theorem Zspec_gcd_gt_aux: forall p n a b cont,
    [a] > [b] -> [a] < 2 ^ (Zpos p + n) ->
      (forall a1 b1, [a1] < 2 ^ n -> [a1] > [b1] ->
            Zis_gcd [a1] [b1] [cont a1 b1]) ->
          Zis_gcd [a] [b] [gcd_gt_aux p cont a b].
 intros p; elim p; clear p.
 intros p Hrec n a b cont H2 H3 H4.
   unfold gcd_gt_aux; apply Zspec_gcd_gt_body with (Zpos (xI p) + n); auto.
   intros a1 b1 H6 H7.
     apply Hrec with (Zpos p + n); auto.
       replace (Zpos p + (Zpos p + n)) with
         (Zpos (xI p) + n  - 1); auto.
       rewrite Zpos_xI; ring.
   intros a2 b2 H9 H10.
     apply Hrec with n; auto.
 intros p Hrec n a b cont H2 H3 H4.
   unfold gcd_gt_aux; apply Zspec_gcd_gt_body with (Zpos (xO p) + n); auto.
   intros a1 b1 H6 H7.
     apply Hrec with (Zpos p + n - 1); auto.
       replace (Zpos p + (Zpos p + n - 1)) with
         (Zpos (xO p) + n  - 1); auto.
       rewrite Zpos_xO; ring.
   intros a2 b2 H9 H10.
     apply Hrec with (n - 1); auto.
       replace (Zpos p + (n - 1)) with
         (Zpos p + n  - 1); auto with zarith.
   intros a3 b3 H12 H13; apply H4; auto with zarith.
    apply Zlt_le_trans with (1 := H12).
    case (Zle_or_lt 1 n); intros HH.
    apply Zpower_le_monotone; auto with zarith.
    apply Zle_trans with 0; auto with zarith.
    assert (HH1: n - 1 < 0); auto with zarith.
    generalize HH1; case (n - 1); auto with zarith.
    intros p1 HH2; discriminate.
 intros n a b cont H H2 H3.
  simpl gcd_gt_aux.
  apply Zspec_gcd_gt_body with (n + 1); auto with zarith.
  rewrite Zplus_comm; auto.
  intros a1 b1 H5 H6; apply H3; auto.
  replace n with (n + 1 - 1); auto; try ring.
 Qed.

 Definition gcd_cont a b :=
  match compare one b with
  | Eq => one
  | _ => a
  end.

 Definition gcd_gt a b := gcd_gt_aux (digits a) gcd_cont a b.

 Theorem spec_gcd_gt: forall a b,
   [a] > [b] -> [gcd_gt a b] = Zgcd [a] [b].
 Proof.
 intros a b H2.
 case (spec_digits (gcd_gt a b)); intros H3 H4.
 case (spec_digits a); intros H5 H6.
 apply sym_equal; apply Zis_gcd_gcd; auto with zarith.
 unfold gcd_gt; apply Zspec_gcd_gt_aux with 0; auto with zarith.
 intros a1 a2; rewrite Zpower_0_r.
 case (spec_digits a2); intros H7 H8;
   intros; apply False_ind; auto with zarith.
 Qed.

 Definition gcd a b :=
  match compare a b with
  | Eq => a
  | Lt => gcd_gt b a
  | Gt => gcd_gt a b
  end.

 Theorem spec_gcd: forall a b, [gcd a b] = Zgcd [a] [b].
 Proof.
 intros a b.
 case (spec_digits a); intros H1 H2.
 case (spec_digits b); intros H3 H4.
 unfold gcd; generalize (spec_compare_aux a b); case compare.
 intros HH; rewrite HH; apply sym_equal; apply Zis_gcd_gcd; auto.
   apply Zis_gcd_refl.
 intros; apply trans_equal with (Zgcd [b] [a]).
   apply spec_gcd_gt; auto with zarith.
 apply Zis_gcd_gcd; auto with zarith.
 apply Zgcd_is_pos.
 apply Zis_gcd_sym; apply Zgcd_is_gcd.
 intros; apply spec_gcd_gt; auto.
 Qed.


 (** * Conversion *)

 Definition of_N x :=
  match x with
  | BinNat.N0 => zero
  | Npos p => of_pos p
  end.

 Theorem spec_of_N: forall x,
   [of_N x] = Z_of_N x.
 Proof.
 intros x; case x.
  simpl of_N.
  unfold zero, w_0, to_Z; rewrite (spec_0 w0_spec); auto.
 intros p; exact (spec_of_pos p).
 Qed.


 (** * Shift *)

 Definition safe_shiftr n x :=
   match compare n (Ndigits x) with
   |  Lt => shiftr n x
   | _ => N0 w_0
   end.

 Theorem spec_safe_shiftr: forall n x,
   [safe_shiftr n x] = [x] / 2 ^ [n].
 Proof.
 intros n x; unfold safe_shiftr;
    generalize (spec_compare_aux n (Ndigits x)); case compare; intros H.
 apply trans_equal with (1 := spec_0 w0_spec).
 apply sym_equal; apply Zdiv_small; rewrite H.
 rewrite spec_Ndigits; exact (spec_digits x).
 rewrite <- spec_shiftr; auto with zarith.
 apply trans_equal with (1 := spec_0 w0_spec).
 apply sym_equal; apply Zdiv_small.
 rewrite spec_Ndigits in H; case (spec_digits x); intros H1 H2.
 split; auto.
 apply Zlt_le_trans with (1 := H2).
 apply Zpower_le_monotone; auto with zarith.
 Qed.

 Definition safe_shiftl_aux_body cont n x :=
   match compare n (head0 x)  with
      Gt => cont n (double_size x)
   |  _ => shiftl n x
   end.

 Theorem spec_safe_shift_aux_body: forall n p x cont,
       2^ Zpos p  <=  [head0 x]  ->
      (forall x, 2 ^ (Zpos p + 1) <= [head0 x]->
         [cont n x] = [x] * 2 ^ [n]) ->
      [safe_shiftl_aux_body cont n x] = [x] * 2 ^ [n].
 Proof.
 intros n p x cont H1 H2; unfold safe_shiftl_aux_body.
 generalize (spec_compare_aux n (head0 x)); case compare; intros H.
  apply spec_shiftl; auto with zarith.
  apply spec_shiftl; auto with zarith.
 rewrite H2.
 rewrite spec_double_size; auto.
 rewrite Zplus_comm; rewrite Zpower_exp; auto with zarith.
 apply Zle_trans with (2 := spec_double_size_head0 x).
 rewrite Zpower_1_r; apply Zmult_le_compat_l; auto with zarith.
 Qed.

 Fixpoint safe_shiftl_aux p cont n x  {struct p} :=
   safe_shiftl_aux_body
       (fun n x => match p with
        | xH => cont n x
        | xO p => safe_shiftl_aux p (safe_shiftl_aux p cont) n x
        | xI p => safe_shiftl_aux p (safe_shiftl_aux p cont) n x
        end) n x.

 Theorem spec_safe_shift_aux: forall p q n x cont,
    2 ^ (Zpos q) <= [head0 x] ->
      (forall x, 2 ^ (Zpos p + Zpos q) <= [head0 x] ->
         [cont n x] = [x] * 2 ^ [n]) ->
      [safe_shiftl_aux p cont n x] = [x] * 2 ^ [n].
 Proof.
 intros p; elim p; unfold safe_shiftl_aux; fold safe_shiftl_aux; clear p.
 intros p Hrec q n x cont H1 H2.
 apply spec_safe_shift_aux_body with (q); auto.
 intros x1 H3; apply Hrec with (q + 1)%positive; auto.
 intros x2 H4; apply Hrec with (p + q + 1)%positive; auto.
 rewrite <- Pplus_assoc.
 rewrite Zpos_plus_distr; auto.
 intros x3 H5; apply H2.
 rewrite Zpos_xI.
 replace (2 * Zpos p + 1 + Zpos q) with (Zpos p + Zpos (p + q + 1));
   auto.
 repeat rewrite Zpos_plus_distr; ring.
 intros p Hrec q n x cont H1 H2.
 apply spec_safe_shift_aux_body with (q); auto.
 intros x1 H3; apply Hrec with (q); auto.
 apply Zle_trans with (2 := H3); auto with zarith.
 apply Zpower_le_monotone; auto with zarith.
 intros x2 H4; apply Hrec with (p + q)%positive; auto.
 intros x3 H5; apply H2.
 rewrite (Zpos_xO p).
 replace (2 * Zpos p + Zpos q) with (Zpos p + Zpos (p + q));
   auto.
 repeat rewrite Zpos_plus_distr; ring.
 intros q n x cont H1 H2.
 apply spec_safe_shift_aux_body with (q); auto.
 rewrite Zplus_comm; auto.
 Qed.

 Definition safe_shiftl n x :=
  safe_shiftl_aux_body
   (safe_shiftl_aux_body
    (safe_shiftl_aux (digits n) shiftl)) n x.

 Theorem spec_safe_shift: forall n x,
   [safe_shiftl n x] = [x] * 2 ^ [n].
 Proof.
 intros n x; unfold safe_shiftl, safe_shiftl_aux_body.
 generalize (spec_compare_aux n (head0 x)); case compare; intros H.
  apply spec_shiftl; auto with zarith.
  apply spec_shiftl; auto with zarith.
 rewrite <- (spec_double_size x).
 generalize (spec_compare_aux n (head0 (double_size x))); case compare; intros H1.
  apply spec_shiftl; auto with zarith.
  apply spec_shiftl; auto with zarith.
 rewrite <- (spec_double_size (double_size x)).
 apply spec_safe_shift_aux with 1%positive.
 apply Zle_trans with (2 := spec_double_size_head0 (double_size x)).
 replace (2 ^ 1) with (2 * 1).
 apply Zmult_le_compat_l; auto with zarith.
 generalize (spec_double_size_head0_pos x); auto with zarith.
 rewrite Zpower_1_r; ring.
 intros x1 H2; apply spec_shiftl.
 apply Zle_trans with (2 := H2).
 apply Zle_trans with (2 ^ Zpos (digits n)); auto with zarith.
 case (spec_digits n); auto with zarith.
 apply Zpower_le_monotone; auto with zarith.
 Qed.


 (** * Zero and One *)

 Theorem spec_0: [zero] = 0.
 Proof.
 exact (spec_0 w0_spec).
 Qed.

 Theorem spec_1: [one] = 1.
 Proof.
 exact (spec_1 w0_spec).
 Qed.


End Make.
