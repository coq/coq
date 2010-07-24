(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
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

Require Import BigNumPrelude ZArith CyclicAxioms DoubleType
  Nbasic Wf_nat StreamMemo NSig NMake_gen.

Module Make (W0:CyclicType) <: NType.

 (** Let's include the macro-generated part. Even if we can't functorize
     things (due to Eval red_t below), the rest of the module only uses
     elements mentionned in interface [NAbstract]. *)

 Include NMake_gen.Make W0.

 Local Notation "[ x ]" := (to_Z x).

 Definition eq (x y : t) := [x] = [y].

 Declare Reduction red_t :=
  lazy beta iota delta
   [iter_t reduce same_level mk_t mk_t_S dom_t dom_op].

 Ltac red_t :=
  match goal with |- ?u => let v := (eval red_t in u) in change v end.

 (** * Generic results *)

 Tactic Notation "destr_t" constr(x) "as" simple_intropattern(pat) :=
  destruct (destr_t x) as pat; cbv zeta;
  rewrite ?iter_mk_t, ?spec_mk_t, ?spec_reduce.

 Lemma spec_same_level : forall A (P:Z->Z->A->Prop)
  (f : forall n, dom_t n -> dom_t n -> A),
  (forall n x y, P (ZnZ.to_Z x) (ZnZ.to_Z y) (f n x y)) ->
  forall x y, P [x] [y] (same_level f x y).
 Proof.
 intros. apply spec_same_level_dep with (P:=fun _ => P); auto.
 Qed.

 Theorem spec_pos: forall x, 0 <= [x].
 Proof.
 intros x. destr_t x as (n,x). now case (ZnZ.spec_to_Z x).
 Qed.

 Lemma digits_dom_op_incr : forall n m, (n<=m)%nat ->
  (ZnZ.digits (dom_op n) <= ZnZ.digits (dom_op m))%positive.
 Proof.
 intros.
 change (Zpos (ZnZ.digits (dom_op n)) <= Zpos (ZnZ.digits (dom_op m))).
 rewrite (digits_dom_op n), (digits_dom_op m).
 apply Zmult_le_compat_l; auto with zarith.
 apply Zpower_le_monotone2; auto with zarith.
 Qed.

 (** * Zero and One *)

 Definition zero := mk_t O ZnZ.zero.
 Definition one := mk_t O ZnZ.one.

 Theorem spec_0: [zero] = 0.
 Proof.
 unfold zero. rewrite spec_mk_t. exact ZnZ.spec_0.
 Qed.

 Theorem spec_1: [one] = 1.
 Proof.
 unfold one. rewrite spec_mk_t. exact ZnZ.spec_1.
 Qed.

 (** * Successor *)

 Local Notation succn := (fun n (x:dom_t n) =>
  let op := dom_op n in
  match ZnZ.succ_c x with
   | C0 r => mk_t n r
   | C1 r => mk_t_S n (WW ZnZ.one r)
  end).

 Definition succ : t -> t := Eval red_t in iter_t succn.

 Lemma succ_fold : succ = iter_t succn.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_succ: forall n, [succ n] = [n] + 1.
 Proof.
  intros x. rewrite succ_fold. destr_t x as (n,x).
  generalize (ZnZ.spec_succ_c x); case ZnZ.succ_c.
  intros. rewrite spec_mk_t. assumption.
  intros. unfold interp_carry in *.
  rewrite spec_mk_t_S. simpl. rewrite ZnZ.spec_1. assumption.
 Qed.

 (** * Addition *)

 Local Notation addn := (fun n (x y : dom_t n) =>
  let op := dom_op n in
  match ZnZ.add_c x y with
  | C0 r => mk_t n r
  | C1 r => mk_t_S n (WW ZnZ.one r)
  end).

 Definition add : t -> t -> t := Eval red_t in same_level addn.

 Lemma add_fold : add = same_level addn.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_add: forall x y, [add x y] = [x] + [y].
 Proof.
  intros x y. rewrite add_fold. apply spec_same_level; clear x y.
  intros n x y. simpl.
  generalize (ZnZ.spec_add_c x y); case ZnZ.add_c; intros z H.
  rewrite spec_mk_t. assumption.
  rewrite spec_mk_t_S. unfold interp_carry in H.
  simpl. rewrite ZnZ.spec_1. assumption.
 Qed.

 (** * Predecessor *)

 Local Notation predn := (fun n (x:dom_t n) =>
  match ZnZ.pred_c x with
   | C0 r => reduce n r
   | C1 _ => zero
  end).

 Definition pred : t -> t := Eval red_t in iter_t predn.

 Lemma pred_fold : pred = iter_t predn.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_pred_pos : forall x, 0 < [x] -> [pred x] = [x] - 1.
 Proof.
  intros x. rewrite pred_fold. destr_t x as (n,x). intros H.
  generalize (ZnZ.spec_pred_c x); case ZnZ.pred_c; intros y H'.
  rewrite spec_reduce. assumption.
  exfalso. unfold interp_carry in *.
  generalize (ZnZ.spec_to_Z x) (ZnZ.spec_to_Z y); auto with zarith.
 Qed.

 Theorem spec_pred0 : forall x, [x] = 0 -> [pred x] = 0.
 Proof.
  intros x. rewrite pred_fold. destr_t x as (n,x). intros H.
  generalize (ZnZ.spec_pred_c x); case ZnZ.pred_c; intros y H'.
  rewrite spec_reduce.
  unfold interp_carry in H'.
  generalize (ZnZ.spec_to_Z y); auto with zarith.
  exact spec_0.
 Qed.

 Lemma spec_pred : forall x, [pred x] = Zmax 0 ([x]-1).
 Proof.
 intros. destruct (Zle_lt_or_eq _ _ (spec_pos x)).
 rewrite Zmax_r; auto with zarith.
 apply spec_pred_pos; auto.
 rewrite <- H; apply spec_pred0; auto.
 Qed.

 (** * Subtraction *)

 Local Notation subn := (fun n (x y : dom_t n) =>
  let op := dom_op n in
  match ZnZ.sub_c x y with
  | C0 r => reduce n r
  | C1 r => zero
  end).

 Definition sub : t -> t -> t := Eval red_t in same_level subn.

 Lemma sub_fold : sub = same_level subn.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_sub_pos : forall x y, [y] <= [x] -> [sub x y] = [x] - [y].
 Proof.
  intros x y. rewrite sub_fold. apply spec_same_level. clear x y.
  intros n x y. simpl.
  generalize (ZnZ.spec_sub_c x y); case ZnZ.sub_c; intros z H LE.
  rewrite spec_reduce. assumption.
  unfold interp_carry in H.
  exfalso.
  generalize (ZnZ.spec_to_Z z); auto with zarith.
 Qed.

 Theorem spec_sub0 : forall x y, [x] < [y] -> [sub x y] = 0.
 Proof.
  intros x y. rewrite sub_fold. apply spec_same_level. clear x y.
  intros n x y. simpl.
  generalize (ZnZ.spec_sub_c x y); case ZnZ.sub_c; intros z H LE.
  rewrite spec_reduce.
  unfold interp_carry in H.
  generalize (ZnZ.spec_to_Z z); auto with zarith.
  exact spec_0.
 Qed.

 Lemma spec_sub : forall x y, [sub x y] = Zmax 0 ([x]-[y]).
 Proof.
 intros. destruct (Zle_or_lt [y] [x]).
 rewrite Zmax_r; auto with zarith. apply spec_sub_pos; auto.
 rewrite Zmax_l; auto with zarith. apply spec_sub0; auto.
 Qed.

 (** * Comparison *)

 Definition eq_bool (x y : t) : bool :=
  match compare x y with
  | Eq => true
  | _  => false
  end.

 Theorem spec_eq_bool : forall x y, eq_bool x y = Zeq_bool [x] [y].
 Proof.
 intros. unfold eq_bool, Zeq_bool. rewrite spec_compare; reflexivity.
 Qed.

 Definition lt (n m : t) := [n] < [m].
 Definition le (n m : t) := [n] <= [m].

 Definition min (n m : t) : t := match compare n m with Gt => m | _ => n end.
 Definition max (n m : t) : t := match compare n m with Lt => m | _ => n end.

 Theorem spec_max : forall n m, [max n m] = Zmax [n] [m].
 Proof.
 intros. unfold max, Zmax. rewrite spec_compare; destruct Zcompare; reflexivity.
 Qed.

 Theorem spec_min : forall n m, [min n m] = Zmin [n] [m].
 Proof.
 intros. unfold min, Zmin. rewrite spec_compare; destruct Zcompare; reflexivity.
 Qed.

 (** * Square *)

 (** TODO: use reduce (original version was using it for N0 only) *)

 Local Notation squaren :=
  (fun n (x : dom_t n) => mk_t_S n (ZnZ.square_c x)).

 Definition square : t -> t := Eval red_t in iter_t squaren.

 Lemma square_fold : square = iter_t squaren.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_square: forall x, [square x] = [x] * [x].
 Proof.
  intros x. rewrite square_fold. destr_t x as (n,x).
  rewrite spec_mk_t_S. exact (ZnZ.spec_square_c x).
 Qed.

 (** * Sqrt *)

 Local Notation sqrtn :=
  (fun n (x : dom_t n) => reduce n (ZnZ.sqrt x)).

 Definition sqrt : t -> t := Eval red_t in iter_t sqrtn.

 Lemma sqrt_fold : sqrt = iter_t sqrtn.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_sqrt: forall x, [sqrt x] ^ 2 <= [x] < ([sqrt x] + 1) ^ 2.
 Proof.
  intros x. rewrite sqrt_fold. destr_t x as (n,x). exact (ZnZ.spec_sqrt x).
 Qed.

 (** * Power *)

 Fixpoint power_pos (x:t)(p:positive) : t :=
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

 Definition power (x:t)(n:N) : t := match n with
  | BinNat.N0 => one
  | BinNat.Npos p => power_pos x p
 end.

 Theorem spec_power: forall x n, [power x n] = [x] ^ Z_of_N n.
 Proof.
 destruct n; simpl. apply spec_1.
 apply spec_power_pos.
 Qed.

 (** * Div *)

 Definition div_eucl (x y : t) : t * t :=
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
 intros x y. unfold div_eucl.
 rewrite spec_eq_bool, spec_compare, spec_0.
 generalize (Zeq_bool_if [y] 0); case Zeq_bool.
 intros ->. rewrite spec_0. destruct [x]; auto.
 intros H'.
 assert (H : 0 < [y]) by (generalize (spec_pos y); auto with zarith).
 clear H'.
 case Zcompare_spec; intros Cmp;
   rewrite ?spec_0, ?spec_1; intros; auto with zarith.
 rewrite Cmp; generalize (Z_div_same [y] (Zlt_gt _ _ H))
                         (Z_mod_same [y] (Zlt_gt _ _ H));
  unfold Zdiv, Zmod; case Zdiv_eucl; intros; subst; auto.
 assert (LeLt: 0 <= [x] < [y]) by (generalize (spec_pos x); auto).
 generalize (Zdiv_small _ _ LeLt) (Zmod_small _ _ LeLt);
  unfold Zdiv, Zmod; case Zdiv_eucl; intros; subst; auto.
 generalize (spec_div_gt _ _ (Zlt_gt _ _ Cmp) H); auto.
 unfold Zdiv, Zmod; case Zdiv_eucl; case div_gt.
 intros a b c d (H1, H2); subst; auto.
 Qed.

 Definition div (x y : t) : t := fst (div_eucl x y).

 Theorem spec_div:
   forall x y, [div x y] = [x] / [y].
 Proof.
 intros x y; unfold div; generalize (spec_div_eucl x y);
   case div_eucl; simpl fst.
 intros xx yy; unfold Zdiv; case Zdiv_eucl; intros qq rr H;
  injection H; auto.
 Qed.

 (** * Modulo *)

 Definition modulo (x y : t) : t :=
  if eq_bool y zero then zero else
  match compare x y with
  | Eq => zero
  | Lt => x
  | Gt => mod_gt x y
  end.

 Theorem spec_modulo:
   forall x y, [modulo x y] = [x] mod [y].
 Proof.
 intros x y. unfold modulo.
 rewrite spec_eq_bool, spec_compare, spec_0.
 generalize (Zeq_bool_if [y] 0). case Zeq_bool.
 intros ->; rewrite spec_0. destruct [x]; auto.
 intro H'.
 assert (H : 0 < [y]) by (generalize (spec_pos y); auto with zarith).
 clear H'.
 case Zcompare_spec;
   rewrite ?spec_0, ?spec_1; intros; try split; auto with zarith.
 rewrite H0; apply sym_equal; apply Z_mod_same; auto with zarith.
 apply sym_equal; apply Zmod_small; auto with zarith.
 generalize (spec_pos x); auto with zarith.
 apply spec_mod_gt; auto with zarith.
 Qed.

 (** * digits

     Number of digits in the representation of a numbers
     (including head zero's).
     NB: This function isn't a morphism for setoid [eq].
 *)

 Local Notation digitsn := (fun n _ => ZnZ.digits (dom_op n)).

 Definition digits : t -> positive := Eval red_t in iter_t digitsn.

 Lemma digits_fold : digits = iter_t digitsn.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_digits: forall x, 0 <= [x] < 2 ^ Zpos (digits x).
 Proof.
 intros x. rewrite digits_fold. destr_t x as (n,x). exact (ZnZ.spec_to_Z x).
 Qed.

 Lemma digits_level : forall x, digits x = ZnZ.digits (dom_op (level x)).
 Proof.
 intros x. rewrite digits_fold. unfold level. destr_t x as (n,x). reflexivity.
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
 intros a b cont p H2 H3 H4; unfold gcd_gt_body.
 rewrite ! spec_compare, spec_0. case Zcompare_spec.
  intros ->; apply Zis_gcd_0.
 intros HH; absurd (0 <= [b]); auto with zarith.
 case (spec_digits b); auto with zarith.
 intros H5; case Zcompare_spec.
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

 Fixpoint gcd_gt_aux (p:positive) (cont:t->t->t) (a b:t) : t :=
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
    apply Zpower_le_monotone2; auto with zarith.
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

 Definition gcd (a b : t) : t :=
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
 unfold gcd. rewrite spec_compare. case Zcompare_spec.
 intros HH; rewrite HH; apply sym_equal; apply Zis_gcd_gcd; auto.
   apply Zis_gcd_refl.
 intros; apply trans_equal with (Zgcd [b] [a]).
   apply spec_gcd_gt; auto with zarith.
 apply Zis_gcd_gcd; auto with zarith.
 apply Zgcd_is_pos.
 apply Zis_gcd_sym; apply Zgcd_is_gcd.
 intros; apply spec_gcd_gt; auto with zarith.
 Qed.

 (** * Conversion *)

 Definition pheight p :=
   Peano.pred (nat_of_P (get_height (ZnZ.digits (dom_op 0)) (plength p))).

 Theorem pheight_correct: forall p,
    Zpos p < 2 ^ (Zpos (ZnZ.digits (dom_op 0)) * 2 ^ (Z_of_nat (pheight p))).
 Proof.
 intros p; unfold pheight.
 assert (F1: forall x, Z_of_nat (Peano.pred (nat_of_P x)) = Zpos x - 1).
  intros x.
  assert (Zsucc (Z_of_nat (Peano.pred (nat_of_P x))) = Zpos x); auto with zarith.
    rewrite <- inj_S.
    rewrite <- (fun x => S_pred x 0); auto with zarith.
    rewrite Zpos_eq_Z_of_nat_o_nat_of_P; auto.
    apply lt_le_trans with 1%nat; auto with zarith.
    exact (le_Pmult_nat x 1).
  rewrite F1; clear F1.
 assert (F2:= (get_height_correct (ZnZ.digits (dom_op 0)) (plength p))).
 apply Zlt_le_trans with (Zpos (Psucc p)).
   rewrite Zpos_succ_morphism; auto with zarith.
  apply Zle_trans with (1 := plength_pred_correct (Psucc p)).
 rewrite Ppred_succ.
 apply Zpower_le_monotone2; auto with zarith.
 Qed.

 Definition of_pos (x:positive) : t  :=
  let n := pheight x in
  reduce n (snd (ZnZ.of_pos x)).

 Theorem spec_of_pos: forall x,
   [of_pos x] = Zpos x.
 Proof.
 intros x; unfold of_pos.
 rewrite spec_reduce.
 simpl.
 apply ZnZ.of_pos_correct.
 unfold base.
 apply Zlt_le_trans with (1 := pheight_correct x).
 apply Zpower_le_monotone2; auto with zarith.
 rewrite (digits_dom_op (_ _)); auto with zarith.
 Qed.

 Definition of_N (x:N) : t :=
  match x with
  | BinNat.N0 => zero
  | Npos p => of_pos p
  end.

 Theorem spec_of_N: forall x,
   [of_N x] = Z_of_N x.
 Proof.
 intros x; case x.
  simpl of_N. exact spec_0.
 intros p; exact (spec_of_pos p).
 Qed.

 Definition to_N (x : t) := Zabs_N (to_Z x).

 (** * [head0] and [tail0]

     Number of zero at the beginning and at the end of
     the representation of the number.
     NB: these functions are not morphism for setoid [eq].
 *)

 Local Notation head0n := (fun n x => reduce n (ZnZ.head0 x)).

 Definition head0 : t -> t := Eval red_t in iter_t head0n.

 Lemma head0_fold : head0 = iter_t head0n.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_head00: forall x, [x] = 0 -> [head0 x] = Zpos (digits x).
 Proof.
 intros x. rewrite head0_fold, digits_fold. destr_t x as (n,x).
 exact (ZnZ.spec_head00 x).
 Qed.

 Lemma pow2_pos_minus_1 : forall z, 0<z -> 2^(z-1) = 2^z / 2.
 Proof.
  intros. apply Zdiv_unique with 0; auto with zarith.
  change 2 with (2^1) at 2.
  rewrite <- Zpower_exp; auto with zarith.
  rewrite Zplus_0_r. f_equal. auto with zarith.
 Qed.

 Theorem spec_head0: forall x, 0 < [x] ->
   2 ^ (Zpos (digits x) - 1) <= 2 ^ [head0 x] * [x] < 2 ^ Zpos (digits x).
 Proof.
 intros x. rewrite pow2_pos_minus_1 by (red; auto).
 rewrite head0_fold, digits_fold. destr_t x as (n,x). exact (ZnZ.spec_head0 x).
 Qed.

 Local Notation tail0n := (fun n x => reduce n (ZnZ.tail0 x)).

 Definition tail0 : t -> t := Eval red_t in iter_t tail0n.

 Lemma tail0_fold : tail0 = iter_t tail0n.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_tail00: forall x, [x] = 0 -> [tail0 x] = Zpos (digits x).
 Proof.
 intros x. rewrite tail0_fold, digits_fold. destr_t x as (n,x).
 exact (ZnZ.spec_tail00 x).
 Qed.

 Theorem spec_tail0: forall x,
   0 < [x] -> exists y, 0 <= y /\ [x] = (2 * y + 1) * 2 ^ [tail0 x].
 Proof.
 intros x. rewrite tail0_fold. destr_t x as (n,x). exact (ZnZ.spec_tail0 x).
 Qed.

 (** * [Ndigits]

     Same as [digits] but encoded using large integers
     NB: this function is not a morphism for setoid [eq].
 *)

 Local Notation Ndigitsn := (fun n _ => reduce n (ZnZ.zdigits (dom_op n))).

 Definition Ndigits : t -> t := Eval red_t in iter_t Ndigitsn.

 Lemma Ndigits_fold : Ndigits = iter_t Ndigitsn.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_Ndigits: forall x, [Ndigits x] = Zpos (digits x).
 Proof.
 intros x. rewrite Ndigits_fold, digits_fold. destr_t x as (n,x).
 apply ZnZ.spec_zdigits.
 Qed.

 (** * Binary logarithm *)

 Local Notation log2n := (fun n x =>
  let op := dom_op n in
  reduce n (ZnZ.sub_carry (ZnZ.zdigits op) (ZnZ.head0 x))).

 Definition log2 : t -> t := Eval red_t in
   fun x => if eq_bool x zero then zero else iter_t log2n x.

 Lemma log2_fold :
   log2 = fun x => if eq_bool x zero then zero else iter_t log2n x.
 Proof. red_t; reflexivity. Qed.

 Lemma spec_log2_0 : forall x, [x] = 0 -> [log2 x] = 0.
 Proof.
 intros x H. rewrite log2_fold.
 rewrite spec_eq_bool, H. rewrite spec_0. simpl. exact spec_0.
 Qed.

 Lemma head0_zdigits : forall n (x : dom_t n),
  0 < ZnZ.to_Z x ->
  ZnZ.to_Z (ZnZ.head0 x) < ZnZ.to_Z (ZnZ.zdigits (dom_op n)).
 Proof.
 intros n x H.
 destruct (ZnZ.spec_head0 x H) as (_,H0).
 intros.
 assert (H1 := ZnZ.spec_to_Z (ZnZ.head0 x)).
 assert (H2 := ZnZ.spec_to_Z (ZnZ.zdigits (dom_op n))).
 unfold base in *.
 rewrite ZnZ.spec_zdigits in H2 |- *.
 set (h := ZnZ.to_Z (ZnZ.head0 x)) in *; clearbody h.
 set (d := ZnZ.digits (dom_op n)) in *; clearbody d.
 destruct (Z_lt_le_dec h (Zpos d)); auto. exfalso.
 assert (1 * 2^Zpos d <= ZnZ.to_Z x * 2^h).
  apply Zmult_le_compat; auto with zarith.
  apply Zpower_le_monotone2; auto with zarith.
 rewrite Zmult_comm in H0. auto with zarith.
 Qed.

 Lemma spec_log2 : forall x, [x]<>0 ->
   2^[log2 x] <= [x] < 2^([log2 x]+1).
 Proof.
 intros x H. rewrite log2_fold.
 rewrite spec_eq_bool. rewrite spec_0.
 generalize (Zeq_bool_if [x] 0). destruct Zeq_bool.
 auto with zarith.
 clear H.
 destr_t x as (n,x). intros H.
 rewrite ZnZ.spec_sub_carry.
 assert (H0 := ZnZ.spec_to_Z x).
 assert (H1 := ZnZ.spec_to_Z (ZnZ.head0 x)).
 assert (H2 := ZnZ.spec_to_Z (ZnZ.zdigits (dom_op n))).
 assert (H3 := head0_zdigits n x).
 rewrite Zmod_small by auto with zarith.
 rewrite (Z.mul_lt_mono_pos_l (2^(ZnZ.to_Z (ZnZ.head0 x))));
  auto with zarith.
 rewrite (Z.mul_le_mono_pos_l _ _ (2^(ZnZ.to_Z (ZnZ.head0 x))));
  auto with zarith.
 rewrite <- 2 Zpower_exp; auto with zarith.
 rewrite Z.add_sub_assoc, Zplus_minus.
 rewrite Z.sub_simpl_r, Zplus_minus.
 rewrite ZnZ.spec_zdigits.
 rewrite pow2_pos_minus_1 by (red; auto).
 apply ZnZ.spec_head0; auto with zarith.
 Qed.

 Lemma log2_digits_head0 : forall x, 0 < [x] ->
   [log2 x] = Zpos (digits x) - [head0 x] - 1.
 Proof.
 intros. rewrite log2_fold.
 rewrite spec_eq_bool. rewrite spec_0.
 generalize (Zeq_bool_if [x] 0). destruct Zeq_bool.
 auto with zarith.
 intros _. revert H. rewrite digits_fold, head0_fold. destr_t x as (n,x).
 rewrite ZnZ.spec_sub_carry.
 intros.
 generalize (head0_zdigits n x H).
 generalize (ZnZ.spec_to_Z (ZnZ.head0 x)).
 generalize (ZnZ.spec_to_Z (ZnZ.zdigits (dom_op n))).
 rewrite ZnZ.spec_zdigits. intros. apply Zmod_small.
 auto with zarith.
 Qed.

 (** * Right shift *)

 Local Notation shiftrn := (fun n (p x : dom_t n) =>
   let op := dom_op n in
   match ZnZ.sub_c (ZnZ.zdigits op) p with
   | C0 d => reduce n (ZnZ.add_mul_div d ZnZ.zero x)
   | C1 _ => zero
   end).

 Definition shiftr : t -> t -> t := Eval red_t in
   same_level shiftrn.

 Lemma shiftr_fold : shiftr = same_level shiftrn.
 Proof. red_t; reflexivity. Qed.

 Lemma div_pow2_bound :forall x y z,
   0 <= x -> 0 <= y -> x < z -> 0 <= x / 2 ^ y < z.
 Proof.
   intros x y z HH HH1 HH2.
   split; auto with zarith.
   apply Zle_lt_trans with (2 := HH2); auto with zarith.
   apply Zdiv_le_upper_bound; auto with zarith.
   pattern x at 1; replace x with (x * 2 ^ 0); auto with zarith.
   apply Zmult_le_compat_l; auto.
   apply Zpower_le_monotone2; auto with zarith.
   rewrite Zpower_0_r; ring.
 Qed.

 Theorem spec_shiftr: forall n x,
  [shiftr n x] = [x] / 2 ^ [n].
 Proof.
  intros x y. rewrite shiftr_fold. apply spec_same_level. clear x y.
  intros n p x. simpl.
  assert (Hx := ZnZ.spec_to_Z p).
  assert (Hy := ZnZ.spec_to_Z x).
  generalize (ZnZ.spec_sub_c (ZnZ.zdigits (dom_op n)) p).
  case ZnZ.sub_c; intros d H; unfold interp_carry in *; simpl.
  (** Subtraction without underflow : [ p <= digits ] *)
  rewrite spec_reduce.
  rewrite ZnZ.spec_zdigits in H.
  rewrite ZnZ.spec_add_mul_div by auto with zarith.
  rewrite ZnZ.spec_0, Zmult_0_l, Zplus_0_l.
  rewrite Zmod_small.
  f_equal. f_equal. auto with zarith.
  split. auto with zarith.
  apply div_pow2_bound; auto with zarith.
  (** Subtraction with underflow : [ digits < p ] *)
  rewrite ZnZ.spec_0. symmetry.
  apply Zdiv_small.
  split; auto with zarith.
  apply Zlt_le_trans with (base (ZnZ.digits (dom_op n))); auto with zarith.
  unfold base. apply Zpower_le_monotone2; auto with zarith.
  rewrite ZnZ.spec_zdigits in H.
  generalize (ZnZ.spec_to_Z d); auto with zarith.
 Qed.

 (** * Left shift *)

 (** First an unsafe version, working correctly only if
     the representation is large enough *)

 Local Notation unsafe_shiftln := (fun n p x =>
   let ops := dom_op n in
   reduce n (ZnZ.add_mul_div p x ZnZ.zero)).

 Definition unsafe_shiftl : t -> t -> t := Eval red_t in
   same_level unsafe_shiftln.

 Lemma unsafe_shiftl_fold : unsafe_shiftl = same_level unsafe_shiftln.
 Proof. red_t; reflexivity. Qed.

 Theorem spec_unsafe_shiftl_aux : forall p x K,
  0 <= K ->
  [x] < 2^K ->
  [p] + K <= Zpos (digits x) ->
  [unsafe_shiftl p x] = [x] * 2 ^ [p].
 Proof.
 intros p x.
 rewrite unsafe_shiftl_fold. rewrite digits_level.
 apply spec_same_level_dep.
 intros n m z z' r LE H K HK H1 H2. apply (H K); auto.
  transitivity (Zpos (ZnZ.digits (dom_op n))); auto.
  apply digits_dom_op_incr; auto.
 clear p x.
 intros n p x K HK Hx Hp. lazy zeta. rewrite spec_reduce.
 destruct (ZnZ.spec_to_Z x).
 destruct (ZnZ.spec_to_Z p).
 rewrite ZnZ.spec_add_mul_div by (omega with *).
 rewrite ZnZ.spec_0, Zdiv_0_l, Zplus_0_r.
 apply Zmod_small. unfold base.
 split; auto with zarith.
 rewrite Zmult_comm.
 apply Zlt_le_trans with (2^(ZnZ.to_Z p + K)).
 rewrite Zpower_exp; auto with zarith.
 apply Zmult_lt_compat_l; auto with zarith.
 apply Zpower_le_monotone2; auto with zarith.
 Qed.

 Theorem spec_unsafe_shiftl: forall p x,
  [p] <= [head0 x] -> [unsafe_shiftl p x] = [x] * 2 ^ [p].
 Proof.
 intros.
 destruct (Z_eq_dec [x] 0) as [EQ|NEQ].
 (* [x] = 0 *)
 apply spec_unsafe_shiftl_aux with 0; auto with zarith.
 now rewrite EQ.
 rewrite spec_head00 in *; auto with zarith.
 (* [x] <> 0 *)
 apply spec_unsafe_shiftl_aux with ([log2 x] + 1); auto with zarith.
 generalize (spec_pos (log2 x)); auto with zarith.
 destruct (spec_log2 x); auto with zarith.
 rewrite log2_digits_head0; auto with zarith.
 generalize (spec_pos x); auto with zarith.
 Qed.

 (** Then we define a function doubling the size of the representation
     but without changing the value of the number. *)

 Local Notation double_size_n :=
  (fun n x => mk_t_S n (WW ZnZ.zero x)).

 Definition double_size : t -> t := Eval red_t in
   iter_t double_size_n.

 Lemma double_size_fold : double_size = iter_t double_size_n.
 Proof. red_t; reflexivity. Qed.

 Lemma double_size_level : forall x, level (double_size x) = S (level x).
 Proof.
 intros x. rewrite double_size_fold; unfold level at 2. destr_t x as (n,x).
 apply mk_t_S_level.
 Qed.

 Theorem spec_double_size_digits:
   forall x, Zpos (digits (double_size x)) = 2 * (Zpos (digits x)).
 Proof.
 intros x. rewrite ! digits_level, double_size_level.
 rewrite !(digits_dom_op (_ _)), inj_S, Zpower_Zsucc; auto with zarith.
 ring.
 Qed.

 Theorem spec_double_size: forall x, [double_size x] = [x].
 Proof.
 intros x. rewrite double_size_fold. destr_t x as (n,x).
 rewrite spec_mk_t_S. simpl. rewrite ZnZ.spec_0. auto with zarith.
 Qed.

 Theorem spec_double_size_head0:
   forall x, 2 * [head0 x] <= [head0 (double_size x)].
 Proof.
 intros x.
 assert (F1:= spec_pos (head0 x)).
 assert (F2: 0 < Zpos (digits x)).
   red; auto.
 case (Zle_lt_or_eq _ _ (spec_pos x)); intros HH.
 generalize HH; rewrite <- (spec_double_size x); intros HH1.
 case (spec_head0 x HH); intros _ HH2.
 case (spec_head0 _ HH1).
 rewrite (spec_double_size x); rewrite (spec_double_size_digits x).
 intros HH3 _.
 case (Zle_or_lt ([head0 (double_size x)]) (2 * [head0 x])); auto; intros HH4.
 absurd (2 ^ (2 * [head0 x] )* [x] < 2 ^ [head0 (double_size x)] * [x]); auto.
 apply Zle_not_lt.
 apply Zmult_le_compat_r; auto with zarith.
 apply Zpower_le_monotone2; auto; auto with zarith.
 assert (HH5: 2 ^[head0 x] <= 2 ^(Zpos (digits x) - 1)).
   case (Zle_lt_or_eq 1 [x]); auto with zarith; intros HH5.
   apply Zmult_le_reg_r with (2 ^ 1); auto with zarith.
   rewrite <- (fun x y z => Zpower_exp x (y - z)); auto with zarith.
   assert (tmp: forall x, x - 1 + 1 = x); [intros; ring | rewrite tmp; clear tmp].
   apply Zle_trans with (2 := Zlt_le_weak _ _ HH2).
   apply Zmult_le_compat_l; auto with zarith.
   rewrite Zpower_1_r; auto with zarith.
   apply Zpower_le_monotone2; auto with zarith.
   case (Zle_or_lt (Zpos (digits x)) [head0 x]); auto with zarith; intros HH6.
   absurd (2 ^ Zpos (digits x) <= 2 ^ [head0 x] * [x]); auto with zarith.
   rewrite <- HH5; rewrite Zmult_1_r.
   apply Zpower_le_monotone2; auto with zarith.
 rewrite (Zmult_comm 2).
 rewrite Zpower_mult; auto with zarith.
 rewrite Zpower_2.
 apply Zlt_le_trans with (2 := HH3).
 rewrite <- Zmult_assoc.
 replace (2 * Zpos (digits x) - 1) with
   ((Zpos (digits x) - 1) + (Zpos (digits x))).
 rewrite Zpower_exp; auto with zarith.
 apply Zmult_lt_compat2; auto with zarith.
 split; auto with zarith.
 apply Zmult_lt_0_compat; auto with zarith.
 rewrite Zpos_xO; ring.
 apply Zlt_le_weak; auto.
 repeat rewrite spec_head00; auto.
 rewrite spec_double_size_digits.
 rewrite Zpos_xO; auto with zarith.
 rewrite spec_double_size; auto.
 Qed.

 Theorem spec_double_size_head0_pos:
   forall x, 0 < [head0 (double_size x)].
 Proof.
 intros x.
 assert (F: 0 < Zpos (digits x)).
  red; auto.
 case (Zle_lt_or_eq _ _ (spec_pos (head0 (double_size x)))); auto; intros F0.
 case (Zle_lt_or_eq _ _ (spec_pos (head0 x))); intros F1.
   apply Zlt_le_trans with (2 := (spec_double_size_head0 x)); auto with zarith.
 case (Zle_lt_or_eq _ _ (spec_pos x)); intros F3.
 generalize F3; rewrite <- (spec_double_size x); intros F4.
 absurd (2 ^ (Zpos (xO (digits x)) - 1) < 2 ^ (Zpos (digits x))).
   apply Zle_not_lt.
   apply Zpower_le_monotone2; auto with zarith.
   rewrite Zpos_xO; auto with zarith.
 case (spec_head0 x F3).
 rewrite <- F1; rewrite Zpower_0_r; rewrite Zmult_1_l; intros _ HH.
 apply Zle_lt_trans with (2 := HH).
 case (spec_head0 _ F4).
 rewrite (spec_double_size x); rewrite (spec_double_size_digits x).
 rewrite <- F0; rewrite Zpower_0_r; rewrite Zmult_1_l; auto.
 generalize F1; rewrite (spec_head00 _ (sym_equal F3)); auto with zarith.
 Qed.

 (** Finally we iterate [double_size] enough before [unsafe_shiftl]
     in order to get a fully correct [shiftl]. *)

 Definition shiftl_aux_body cont n x :=
   match compare n (head0 x)  with
      Gt => cont n (double_size x)
   |  _ => unsafe_shiftl n x
   end.

 Theorem spec_shiftl_aux_body: forall n p x cont,
       2^ Zpos p  <=  [head0 x]  ->
      (forall x, 2 ^ (Zpos p + 1) <= [head0 x]->
         [cont n x] = [x] * 2 ^ [n]) ->
      [shiftl_aux_body cont n x] = [x] * 2 ^ [n].
 Proof.
 intros n p x cont H1 H2; unfold shiftl_aux_body.
 rewrite spec_compare; case Zcompare_spec; intros H.
  apply spec_unsafe_shiftl; auto with zarith.
  apply spec_unsafe_shiftl; auto with zarith.
 rewrite H2.
 rewrite spec_double_size; auto.
 rewrite Zplus_comm; rewrite Zpower_exp; auto with zarith.
 apply Zle_trans with (2 := spec_double_size_head0 x).
 rewrite Zpower_1_r; apply Zmult_le_compat_l; auto with zarith.
 Qed.

 Fixpoint shiftl_aux p cont n x :=
   shiftl_aux_body
       (fun n x => match p with
        | xH => cont n x
        | xO p => shiftl_aux p (shiftl_aux p cont) n x
        | xI p => shiftl_aux p (shiftl_aux p cont) n x
        end) n x.

 Theorem spec_shiftl_aux: forall p q n x cont,
    2 ^ (Zpos q) <= [head0 x] ->
      (forall x, 2 ^ (Zpos p + Zpos q) <= [head0 x] ->
         [cont n x] = [x] * 2 ^ [n]) ->
      [shiftl_aux p cont n x] = [x] * 2 ^ [n].
 Proof.
 intros p; elim p; unfold shiftl_aux; fold shiftl_aux; clear p.
 intros p Hrec q n x cont H1 H2.
 apply spec_shiftl_aux_body with (q); auto.
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
 apply spec_shiftl_aux_body with (q); auto.
 intros x1 H3; apply Hrec with (q); auto.
 apply Zle_trans with (2 := H3); auto with zarith.
 apply Zpower_le_monotone2; auto with zarith.
 intros x2 H4; apply Hrec with (p + q)%positive; auto.
 intros x3 H5; apply H2.
 rewrite (Zpos_xO p).
 replace (2 * Zpos p + Zpos q) with (Zpos p + Zpos (p + q));
   auto.
 repeat rewrite Zpos_plus_distr; ring.
 intros q n x cont H1 H2.
 apply spec_shiftl_aux_body with (q); auto.
 rewrite Zplus_comm; auto.
 Qed.

 Definition shiftl n x :=
  shiftl_aux_body
   (shiftl_aux_body
    (shiftl_aux (digits n) unsafe_shiftl)) n x.

 Theorem spec_shiftl: forall n x,
   [shiftl n x] = [x] * 2 ^ [n].
 Proof.
 intros n x; unfold shiftl, shiftl_aux_body.
 rewrite spec_compare; case Zcompare_spec; intros H.
  apply spec_unsafe_shiftl; auto with zarith.
  apply spec_unsafe_shiftl; auto with zarith.
 rewrite <- (spec_double_size x).
 rewrite spec_compare; case Zcompare_spec; intros H1.
  apply spec_unsafe_shiftl; auto with zarith.
  apply spec_unsafe_shiftl; auto with zarith.
 rewrite <- (spec_double_size (double_size x)).
 apply spec_shiftl_aux with 1%positive.
 apply Zle_trans with (2 := spec_double_size_head0 (double_size x)).
 replace (2 ^ 1) with (2 * 1).
 apply Zmult_le_compat_l; auto with zarith.
 generalize (spec_double_size_head0_pos x); auto with zarith.
 rewrite Zpower_1_r; ring.
 intros x1 H2; apply spec_unsafe_shiftl.
 apply Zle_trans with (2 := H2).
 apply Zle_trans with (2 ^ Zpos (digits n)); auto with zarith.
 case (spec_digits n); auto with zarith.
 apply Zpower_le_monotone2; auto with zarith.
 Qed.

 (** * Parity test *)

 Definition is_even : t -> bool := Eval red_t in
   iter_t (fun n x => ZnZ.is_even x).

 Lemma is_even_fold : is_even = iter_t (fun n x => ZnZ.is_even x).
 Proof. red_t; reflexivity. Qed.

 Theorem spec_is_even: forall x,
   if is_even x then [x] mod 2 = 0 else [x] mod 2 = 1.
 Proof.
 intros x. rewrite is_even_fold. destr_t x as (n,x).
 exact (ZnZ.spec_is_even x).
 Qed.

End Make.
