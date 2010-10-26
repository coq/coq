Require Import Zgcd_alt.
Require Import Bvector.
Require Export Int31Axioms.
Require Import Eqdep_dec.

Local Open Scope int31_scope.
Local Open Scope Z_scope.
(** Trivial lemmas without axiom *)

Lemma wB_diff_0 : wB <> 0.
Proof. compute;discriminate. Qed.

Lemma wB_pos : 0 < wB.
Proof. reflexivity. Qed.

Lemma to_Z_0 : [|0|] = 0.
Proof. reflexivity. Qed.

Lemma to_Z_1 : [|1|] = 1.
Proof. reflexivity. Qed.

(** equality *)
Lemma eqb_complete : forall x y, x = y -> (x == y) = true.
Proof.
 intros x y H;rewrite H, eqb_refl;trivial.
Qed.

Lemma eqb_spec : forall x y, (x == y) = true <-> x = y.
Proof.
 split;auto using eqb_correct, eqb_complete.
Qed.

Lemma eqb_false_spec : forall x y, (x == y) = false <-> x <> y.
Proof.
 intros;rewrite <- not_true_iff_false, eqb_spec;split;trivial.
Qed.

Lemma eqb_false_complete : forall x y, x <> y -> (x == y) = false.
Proof.
 intros x y;rewrite eqb_false_spec;trivial. 
Qed.

Lemma eqb_false_correct : forall x y, (x == y) = false -> x <> y.
Proof.
 intros x y;rewrite eqb_false_spec;trivial.
Qed.  
 
Definition eqs (i j : int) : {i = j} + { i <> j } := 
  (if i == j as b return ((b = true -> i = j) -> (b = false -> i <> j) -> {i=j} + {i <> j} )
    then fun (Heq : true = true -> i = j) _ => left _ (Heq (eq_refl true))
    else fun _ (Hdiff : false = false -> i <> j) => right _ (Hdiff (eq_refl false)))
  (eqb_correct i j)
  (eqb_false_correct i j).

Lemma eq_dec : forall i j:int, i = j \/ i <> j.
Proof.
 intros i j;destruct (eqs i j);auto.
Qed.

Lemma cast_refl : forall i, cast i i = Some (fun P H => H).
Proof.
 unfold cast;intros.
 generalize (eqb_correct i i).
 rewrite eqb_refl;intros.
 rewrite (eq_proofs_unicity eq_dec (e (eq_refl true)) (eq_refl i));trivial.
Qed.

Lemma cast_diff : forall i j, i == j = false -> cast i j = None.
Proof.
 intros;unfold cast;intros; generalize (eqb_correct i j).
 rewrite H;trivial.
Qed.

Lemma eqo_refl : forall i, eqo i i = Some (eq_refl i).
Proof.
 unfold eqo;intros.
 generalize (eqb_correct i i).
 rewrite eqb_refl;intros.
 rewrite (eq_proofs_unicity eq_dec (e (eq_refl true)) (eq_refl i));trivial.
Qed.

Lemma eqo_diff : forall i j, i == j = false -> eqo i j = None.
Proof.
 unfold eqo;intros; generalize (eqb_correct i j).
 rewrite H;trivial. 
Qed.

(** translation with Z *)
Require Import Ndigits.

Lemma Z_of_N_double : forall n, Z_of_N (Ndouble n) = Zdouble (Z_of_N n).
Proof.
 destruct n;simpl;trivial.
Qed.

Lemma Z_of_N_double_plus_one : forall n, Z_of_N (Ndouble_plus_one n) = Zdouble_plus_one (Z_of_N n).
Proof.
 destruct n;simpl;trivial.
Qed.

Lemma to_Z_bounded : forall x, 0 <= [|x|] < wB.
Proof.
 unfold to_Z, wB;induction size;intros.
 simpl;auto with zarith.
 rewrite inj_S;simpl;assert (W:= IHn (x >> 1)%int31).
 rewrite Zpower_Zsucc;auto with zarith.
 destruct (is_even x).
 rewrite Zdouble_mult;auto with zarith.
 rewrite Zdouble_plus_one_mult;auto with zarith.
Qed.

(* TODO: move_this *)
Lemma orb_true_iff : forall b1 b2, b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
 split;intros;[apply orb_prop | apply orb_true_intro];trivial.
Qed.

Lemma to_Z_eq : forall x y, [|x|] = [|y|] <-> x = y.
Proof.
 split;intros;subst;trivial.
 apply to_Z_inj;trivial.
Qed.

Lemma leb_ltb_eqb : forall x y, ((x <= y) = (x < y) || (x == y))%int31.
Proof.
 intros.
 apply eq_true_iff_eq.
 rewrite leb_spec, orb_true_iff, ltb_spec, eqb_spec, <- to_Z_eq;omega.
Qed.


(** Comparison *)

Lemma compare_spec :
  forall x y, compare x y = ([|x|] ?= [|y|]).
Proof.
 intros;rewrite compare_def_spec;unfold compare_def.
 case_eq (x < y)%int31;intros Heq.
 rewrite ltb_spec in Heq.
 red in Heq;rewrite Heq;trivial.
 rewrite <- not_true_iff_false, ltb_spec in Heq.
 case_eq (x == y)%int31;intros Heq1.
 rewrite eqb_spec in Heq1;rewrite Heq1, Zcompare_refl;trivial.
 rewrite <- not_true_iff_false, eqb_spec in Heq1.
 symmetry;change ([|x|] > [|y|]);rewrite <- to_Z_eq in Heq1;omega.
Qed.

Lemma is_zero_spec : forall x : int, is_zero x = true <-> x = 0%int31.
Proof.
 unfold is_zero;intros;apply eqb_spec.
Qed.


(** Addition *)

Lemma addc_spec  : forall x y, [+|x +c y|] = [|x|] + [|y|].
Proof.
 intros;rewrite addc_def_spec;unfold addc_def.
 assert (W1 := to_Z_bounded x); assert (W2 := to_Z_bounded y).
 case_eq ((x + y < x)%int31).
 rewrite ltb_spec;intros.
 change (wB + [|x+y|] = [|x|] + [|y|]).
 rewrite add_spec in H |- *.
 assert ([|x|] + [|y|] >= wB).
  destruct (Z_lt_ge_dec ([|x|] + [|y|]) wB);auto with zarith.
  elimtype False;rewrite Zmod_small in H;auto with zarith.
 assert (([|x|] + [|y|]) mod wB = [|x|] + [|y|] - wB).
  symmetry;apply Zmod_unique with 1;auto with zarith.
 rewrite H1;ring.
 rewrite <- not_true_iff_false, ltb_spec;intros.
 change ([|x+y|] = [|x|] + [|y|]).
 rewrite add_spec in *.
 assert ([|x|] + [|y|] < wB).
  destruct (Z_lt_ge_dec ([|x|] + [|y|]) wB);auto with zarith.
  assert (([|x|] + [|y|]) mod wB = [|x|] + [|y|] - wB).
  symmetry;apply Zmod_unique with 1;auto with zarith.
  elim H;omega.
 rewrite Zmod_small;auto with zarith.
Qed.

Lemma succc_spec : forall x, [+|succc x|] = [|x|] + 1.
Proof. intros; apply addc_spec. Qed.

Lemma addcarry_spec : forall x y, [|addcarry x y|] = ([|x|] + [|y|] + 1) mod wB.
Proof.
 unfold addcarry;intros.
 rewrite add_spec,add_spec,Zplus_mod_idemp_l;trivial.
Qed.

Lemma addcarryc_spec : forall x y, [+|addcarryc x y|] = [|x|] + [|y|] + 1.
Proof.
 intros;rewrite addcarryc_def_spec;unfold addcarryc_def.
 assert (W1 := to_Z_bounded x); assert (W2 := to_Z_bounded y).
 case_eq ((addcarry x y <= x)%int31).
 rewrite leb_spec;intros.
 change (wB + [|(addcarry x y)|] = [|x|] + [|y|] + 1).
 rewrite addcarry_spec in H |- *.
 assert ([|x|] + [|y|] + 1 >= wB).
  destruct (Z_lt_ge_dec ([|x|] + [|y|] + 1) wB);auto with zarith.
  elimtype False;rewrite Zmod_small in H;auto with zarith.
 assert (([|x|] + [|y|] + 1) mod wB = [|x|] + [|y|] + 1 - wB).
  symmetry;apply Zmod_unique with 1;auto with zarith.
 rewrite H1;ring.
 rewrite <- not_true_iff_false, leb_spec;intros.
 change ([|addcarry x y|] = [|x|] + [|y|] + 1).
 rewrite addcarry_spec in *.
 assert ([|x|] + [|y|] + 1 < wB).
  destruct (Z_lt_ge_dec ([|x|] + [|y|] + 1) wB);auto with zarith.
  assert (([|x|] + [|y|] + 1) mod wB = [|x|] + [|y|] + 1 - wB).
  symmetry;apply Zmod_unique with 1;auto with zarith.
  elim H;omega.
 rewrite Zmod_small;auto with zarith.
Qed.

Lemma succ_spec : forall x, [|succ x|] = ([|x|] + 1) mod wB.
Proof. intros; apply add_spec. Qed.

(** Subtraction *)
Lemma subc_spec : forall x y, [-|x -c y|] = [|x|] - [|y|].
Proof.
 intros;rewrite subc_def_spec;unfold subc_def.
 assert (W1 := to_Z_bounded x); assert (W2 := to_Z_bounded y).
 case_eq (y <= x)%int31.
 rewrite leb_spec;intros.
 change ([|x - y|] = [|x|] - [|y|]).
 rewrite sub_spec.
 rewrite Zmod_small;auto with zarith.
 rewrite <- not_true_iff_false, leb_spec;intros.
 change (-wB + [|x - y|] = [|x|] - [|y|]).
 rewrite sub_spec.
 assert (([|x|] - [|y|]) mod wB = [|x|] - [|y|] + wB).
  symmetry;apply Zmod_unique with (-1);auto with zarith.
 rewrite H0;ring.
Qed.

Lemma subcarry_spec :
   forall x y, [|subcarry x y|] = ([|x|] - [|y|] - 1) mod wB.
Proof. 
 unfold subcarry; intros.
 rewrite sub_spec,sub_spec,Zminus_mod_idemp_l;trivial.
Qed.

Lemma subcarryc_spec : forall x y, [-|subcarryc x y|] = [|x|] - [|y|] - 1.
 intros;rewrite subcarryc_def_spec;unfold subcarryc_def.
 assert (W1 := to_Z_bounded x); assert (W2 := to_Z_bounded y).
 fold (subcarry x y).
 case_eq (y < x)%int31.
 rewrite ltb_spec;intros.
 change ([|subcarry x y|] = [|x|] - [|y|] - 1).
 rewrite subcarry_spec.
 rewrite Zmod_small;auto with zarith.
 rewrite <- not_true_iff_false, ltb_spec;intros.
 change (-wB + [|subcarry x y|] = [|x|] - [|y|] - 1).
 rewrite subcarry_spec.
 assert (([|x|] - [|y|] - 1) mod wB = [|x|] - [|y|] - 1 + wB).
  symmetry;apply Zmod_unique with (-1);auto with zarith.
 rewrite H0;ring.
Qed.

Lemma oppc_spec : forall x : int, [-|oppc x|] = - [|x|].
Proof.
 unfold oppc;intros;rewrite subc_spec, to_Z_0;trivial.
Qed.

Lemma opp_spec : forall x : int, [|- x|] = - [|x|] mod wB.
Proof.
 unfold opp;intros;rewrite sub_spec, to_Z_0;trivial.
Qed.

Lemma oppcarry_spec : forall x, [|oppcarry x|] = wB - [|x|] - 1.
Proof.
 unfold oppcarry;intros.
 rewrite sub_spec.
 change [|max_int|] with (wB - 1).
 rewrite <- Zminus_plus_distr, Zplus_comm, Zminus_plus_distr.
 apply Zmod_small.
 generalize (to_Z_bounded x);auto with zarith.
Qed.

Lemma predc_spec : forall x, [-|predc x|] = [|x|] - 1.
Proof. intros; apply subc_spec. Qed.

Lemma pred_spec : forall x, [|pred x|] = ([|x|] - 1) mod wB.
Proof. intros; apply sub_spec. Qed.

Lemma diveucl_spec : 
  forall x y, 
    let (q,r) := diveucl x y in
    ([|q|],[|r|]) = Zdiv_eucl [|x|] [|y|].
Proof.
 intros;rewrite diveucl_def_spec.
 unfold diveucl_def;rewrite div_spec, mod_spec.
 unfold Zdiv, Zmod;destruct (Zdiv_eucl [|x|] [|y|]);trivial.
Qed.

(* Sqrt *)

 (* Direct transcription of an old proof
     of a fortran program in boyer-moore *)

Lemma quotient_by_2 a: a - 1 <= (a/2) + (a/2).
Proof.
 case (Z_mod_lt a 2); auto with zarith.
 intros H1; rewrite Zmod_eq_full; auto with zarith.
Qed.

Lemma sqrt_main_trick j k: 0 <= j -> 0 <= k ->
   (j * k) + j <= ((j + k)/2 + 1)  ^ 2.
Proof.
 intros Hj; generalize Hj k; pattern j; apply natlike_ind;
   auto; clear k j Hj.
 intros _ k Hk; repeat rewrite Zplus_0_l.
 apply  Zmult_le_0_compat; generalize (Z_div_pos k 2); auto with zarith.
 intros j Hj Hrec _ k Hk; pattern k; apply natlike_ind; auto; clear k Hk.
 rewrite Zmult_0_r, Zplus_0_r, Zplus_0_l.
 generalize (sqr_pos (Zsucc j / 2)) (quotient_by_2 (Zsucc j));
   unfold Zsucc.
 rewrite Zpower_2, Zmult_plus_distr_l; repeat rewrite Zmult_plus_distr_r.
 auto with zarith.
 intros k Hk _.
 replace ((Zsucc j + Zsucc k) / 2) with ((j + k)/2 + 1).
 generalize (Hrec Hj k Hk) (quotient_by_2 (j + k)).
 unfold Zsucc; repeat rewrite Zpower_2;
   repeat rewrite Zmult_plus_distr_l; repeat rewrite Zmult_plus_distr_r.
 repeat rewrite Zmult_1_l; repeat rewrite Zmult_1_r.
 auto with zarith.
 rewrite Zplus_comm, <- Z_div_plus_full_l; auto with zarith.
 apply f_equal2 with (f := Zdiv); auto with zarith.
Qed.

Lemma sqrt_main i j: 0 <= i -> 0 < j -> i < ((j + (i/j))/2 + 1) ^ 2.
Proof.
 intros Hi Hj.
 assert (Hij: 0 <= i/j) by (apply Z_div_pos; auto with zarith).
 apply Zlt_le_trans with (2 := sqrt_main_trick _ _ (Zlt_le_weak _ _ Hj) Hij).
 pattern i at 1; rewrite (Z_div_mod_eq i j); case (Z_mod_lt i j); auto with zarith.
Qed.

Lemma sqrt_init i: 1 < i -> i < (i/2 + 1) ^ 2.
Proof.
 intros Hi.
 assert (H1: 0 <= i - 2) by auto with zarith.
 assert (H2: 1 <= (i / 2) ^ 2); auto with zarith.
   replace i with (1* 2 + (i - 2)); auto with zarith.
   rewrite Zpower_2, Z_div_plus_full_l; auto with zarith.
   generalize (sqr_pos ((i - 2)/ 2)) (Z_div_pos (i - 2) 2).
   rewrite Zmult_plus_distr_l; repeat rewrite Zmult_plus_distr_r.
   auto with zarith.
 generalize (quotient_by_2 i).
 rewrite Zpower_2 in H2 |- *;
   repeat (rewrite Zmult_plus_distr_l ||
           rewrite Zmult_plus_distr_r ||
           rewrite Zmult_1_l || rewrite Zmult_1_r).
   auto with zarith.
Qed.

Lemma sqrt_test_true i j: 0 <= i -> 0 < j -> i/j >= j -> j ^ 2 <= i.
Proof.
 intros Hi Hj Hd; rewrite Zpower_2.
 apply Zle_trans with (j * (i/j)); auto with zarith.
 apply Z_mult_div_ge; auto with zarith.
Qed.

Lemma sqrt_test_false i j: 0 <= i -> 0 < j -> i/j < j ->  (j + (i/j))/2 < j.
Proof.
 intros Hi Hj H; case (Zle_or_lt j ((j + (i/j))/2)); auto.
 intros H1; contradict H; apply Zle_not_lt.
 assert (2 * j <= j + (i/j)); auto with zarith.
 apply Zle_trans with (2 * ((j + (i/j))/2)); auto with zarith.
 apply Z_mult_div_ge; auto with zarith.
Qed.

Lemma sqrt_step_correct rec i j:
  0 < [|i|] -> 0 < [|j|] -> [|i|] < ([|j|] + 1) ^ 2 ->
   2 * [|j|] < wB ->
  (forall j1 : int,
    0 < [|j1|] < [|j|] -> [|i|] < ([|j1|] + 1) ^ 2 ->
    [|rec i j1|] ^ 2 <= [|i|] < ([|rec i j1|] + 1) ^ 2) ->
  [|sqrt_step rec i j|] ^ 2 <= [|i|] < ([|sqrt_step rec i j|] + 1) ^ 2.
Proof.
 assert (Hp2: 0 < [|2|]) by exact (refl_equal Lt).
 intros Hi Hj Hij H31 Hrec.
 unfold sqrt_step.
 case_eq ((i / j < j)%int31);[ | rewrite <- Bool.not_true_iff_false];
  rewrite ltb_spec, div_spec;intros.
 assert ([| j + i / j|] = [|j|] + [|i|]/[|j|]).
   rewrite add_spec, Zmod_small;rewrite div_spec;auto with zarith.
 apply Hrec;rewrite lsr_spec, H0, to_Z_1;change (2^1) with 2.
 split; [ | apply sqrt_test_false;auto with zarith].
 replace ([|j|] + [|i|]/[|j|]) with
        (1 * 2 + (([|j|] - 2) + [|i|] / [|j|]));[ | ring].
 rewrite Z_div_plus_full_l; auto with zarith.
 assert (0 <= [|i|]/ [|j|]) by (apply Z_div_pos; auto with zarith).
 assert (0 <= ([|j|] - 2 + [|i|] / [|j|]) / 2) ; auto with zarith.
 case (Zle_lt_or_eq 1 [|j|]); auto with zarith; intros Hj1.
 rewrite <- Hj1, Zdiv_1_r.
 assert (0 <= ([|i|] - 1) /2)%Z;[ |apply Z_div_pos]; auto with zarith.
 apply sqrt_main;auto with zarith.
 split;[apply sqrt_test_true | ];auto with zarith.
Qed.
 
Lemma iter_sqrt_correct n rec i j: 0 < [|i|] -> 0 < [|j|] ->
  [|i|] < ([|j|] + 1) ^ 2 -> 2 * [|j|] < wB ->
  (forall j1, 0 < [|j1|] -> 2^(Z_of_nat n) + [|j1|] <= [|j|] ->
      [|i|] < ([|j1|] + 1) ^ 2 -> 2 * [|j1|] < wB ->
       [|rec i j1|] ^ 2 <= [|i|] < ([|rec i j1|] + 1) ^ 2) ->
  [|iter_sqrt n rec i j|] ^ 2 <= [|i|] < ([|iter_sqrt n rec i j|] + 1) ^ 2.
Proof.
 revert rec i j; elim n; unfold iter_sqrt; fold iter_sqrt; clear n.
 intros rec i j Hi Hj Hij H31 Hrec; apply sqrt_step_correct; auto with zarith.
 intros; apply Hrec; auto with zarith.
 rewrite Zpower_0_r; auto with zarith.
 intros n Hrec rec i j Hi Hj Hij H31 HHrec.
 apply sqrt_step_correct; auto.
 intros j1 Hj1  Hjp1; apply Hrec; auto with zarith.
 intros j2 Hj2 H2j2 Hjp2 Hj31; apply Hrec; auto with zarith.
 intros j3 Hj3 Hpj3.
 apply HHrec; auto.
 rewrite inj_S, Zpower_Zsucc.
 apply Zle_trans with (2 ^Z_of_nat n + [|j2|]); auto with zarith.
 apply Zle_0_nat.
Qed.

Lemma sqrt_spec : forall x,
       [|sqrt x|] ^ 2 <= [|x|] < ([|sqrt x|] + 1) ^ 2.
Proof.
 intros i; unfold sqrt.
 rewrite compare_spec. case Zcompare_spec; rewrite to_Z_1;
   intros Hi; auto with zarith.
 repeat rewrite Zpower_2; auto with zarith.
 apply iter_sqrt_correct; auto with zarith;
  rewrite lsr_spec, to_Z_1; change (2^1) with 2;  auto with zarith.
  replace ([|i|]) with (1 * 2 + ([|i|] - 2))%Z; try ring.
  assert (0 <= ([|i|] - 2)/2)%Z by (apply Z_div_pos; auto with zarith).
  rewrite Z_div_plus_full_l; auto with zarith.
  apply sqrt_init; auto.
  assert (W:= Z_mult_div_ge [|i|] 2);assert (W':= to_Z_bounded i);auto with zarith.
  intros j2 H1 H2; contradict H2; apply Zlt_not_le.
  fold wB;assert (W:=to_Z_bounded i).
  apply Zle_lt_trans with ([|i|]); auto with zarith.
  assert (0 <= [|i|]/2)%Z by (apply Z_div_pos; auto with zarith).
  apply Zle_trans with (2 * ([|i|]/2)); auto with zarith.
  apply Z_mult_div_ge; auto with zarith.
 case (to_Z_bounded i); repeat rewrite Zpower_2; auto with zarith.
Qed.

Lemma sqrt2_step_def rec ih il j:
   sqrt2_step rec ih il j =
   if (ih < j)%int31 then
    let quo := fst (diveucl_21 ih il j) in
    if (quo < j)%int31 then
     let m :=
      match j +c quo with
      | C0 m1 => m1 >> 1
      | C1 m1 => (m1 >> 1 + 1 << (digits -1))%int31
      end in
     rec ih il m
    else j
   else j.
Proof.
 unfold sqrt2_step; case diveucl_21; intros;simpl.
 case (j +c i);trivial.
Qed.

Lemma sqrt2_lower_bound ih il j:
   [|| WW ih il||]  < ([|j|] + 1) ^ 2 -> [|ih|] <= [|j|].
Proof.
 intros H1.
 case (to_Z_bounded j); intros Hbj _.
 case (to_Z_bounded il); intros Hbil _.
 case (to_Z_bounded ih); intros Hbih Hbih1.
 assert (([|ih|] < [|j|] + 1)%Z); auto with zarith.
 apply Zlt_square_simpl; auto with zarith.
 simpl zn2z_to_Z in H1.
 repeat rewrite <-Zpower_2; apply Zle_lt_trans with (2 := H1).
 apply Zle_trans with ([|ih|] * wB)%Z;try rewrite Zpower_2; auto with zarith.
Qed.

Lemma div2_phi ih il j: 
  [|fst (diveucl_21 ih il j)|] = [|| WW ih il||] /[|j|].
Proof.
 generalize (diveucl_21_spec ih il j).
 case diveucl_21; intros q r Heq.
 simpl zn2z_to_Z;unfold Zdiv;rewrite <- Heq;trivial.
Qed.

Lemma zn2z_to_Z_pos ih il : 0 <= [||WW ih il||].
Proof.
 simpl zn2z_to_Z;destruct (to_Z_bounded ih);destruct (to_Z_bounded il);auto with zarith.
Qed.


Lemma sqrt2_step_correct rec ih il j:
  2 ^ (Z_of_nat (size - 2)) <= [|ih|] -> 
  0 < [|j|] -> [|| WW ih il||] < ([|j|] + 1) ^ 2 ->
  (forall j1, 0 < [|j1|] < [|j|] ->  [|| WW ih il||] < ([|j1|] + 1) ^ 2 ->
     [|rec ih il j1|] ^ 2 <= [||WW ih il||] < ([|rec ih il j1|] + 1) ^ 2) ->
  [|sqrt2_step rec ih il j|] ^ 2 <= [||WW ih il ||]
      < ([|sqrt2_step rec ih il j|] + 1) ^  2.
Proof.
 assert (Hp2: (0 < [|2|])%Z) by exact (refl_equal Lt).
 intros Hih Hj Hij Hrec; rewrite sqrt2_step_def.
 assert (H1: ([|ih|] <= [|j|])%Z) by (apply sqrt2_lower_bound with il; auto).
 case (to_Z_bounded ih); intros Hih1 _.
 case (to_Z_bounded il); intros Hil1 _.
 case (to_Z_bounded j); intros _ Hj1.
 assert (Hp3: (0 < [||WW ih il||])).
  simpl zn2z_to_Z;apply Zlt_le_trans with ([|ih|] * wB)%Z; auto with zarith.
  apply Zmult_lt_0_compat; auto with zarith.
  apply Zlt_le_trans with (2:= Hih); auto with zarith.
 cbv zeta.
 case_eq (ih < j)%int31;intros Heq.
 rewrite ltb_spec in Heq.
 2: rewrite <-not_true_iff_false, ltb_spec in Heq.
 2: split; auto.
 2: apply sqrt_test_true; auto with zarith.
 2: unfold zn2z_to_Z; replace [|ih|] with [|j|]; auto with zarith.
 2: assert (0 <= [|il|]/[|j|]) by (apply Z_div_pos; auto with zarith).
 2: rewrite Zmult_comm, Z_div_plus_full_l; unfold base; auto with zarith.
 case (Zle_or_lt (2^(Z_of_nat size -1)) [|j|]); intros Hjj.
 case_eq (fst (diveucl_21 ih il j) < j)%int31;intros Heq0.
 2: rewrite <-not_true_iff_false, ltb_spec, div2_phi in Heq0.
 2: split; auto; apply sqrt_test_true; auto with zarith.
 rewrite ltb_spec, div2_phi in Heq0.
 match goal with |- context[rec _ _ ?X] =>
  set (u := X)
 end. 
 assert (H: [|u|] = ([|j|] + ([||WW ih il||])/([|j|]))/2).
  unfold u; generalize (addc_spec j (fst (diveucl_21 ih il j)));
  case addc;unfold interp_carry;rewrite div2_phi;simpl zn2z_to_Z.
  intros i H;rewrite lsr_spec, H;trivial.
  intros i H;rewrite <- H.
  case (to_Z_bounded i); intros H1i H2i.
  rewrite add_spec, Zmod_small, lsr_spec.
  change (1 * wB) with ([|(1 << (digits -1))|] * 2)%Z.
  rewrite Z_div_plus_full_l; auto with zarith.
  change wB with (2 * (wB/2))%Z; auto.
  replace [|(1 << (digits - 1))|] with (wB/2); auto.
  rewrite lsr_spec; auto.
  replace (2^[|1|]) with 2%Z; auto.
  split; auto with zarith.
  assert ([|i|]/2 < wB/2); auto with zarith.
  apply Zdiv_lt_upper_bound; auto with zarith.
 apply Hrec; rewrite H; clear u H.
 assert (Hf1: 0 <= [||WW ih il||]/ [|j|]) by (apply Z_div_pos; auto with zarith).
 case (Zle_lt_or_eq 1 ([|j|])); auto with zarith; intros Hf2.
 2: contradict Heq0; apply Zle_not_lt; rewrite <- Hf2, Zdiv_1_r; auto with zarith.
 split.
 replace ([|j|] + [||WW ih il||]/ [|j|])%Z with
        (1 * 2 + (([|j|] - 2) + [||WW ih il||] / [|j|])); try ring.
 rewrite Z_div_plus_full_l; auto with zarith.
 assert (0 <= ([|j|] - 2 + [||WW ih il||] / [|j|]) / 2) ; auto with zarith.
 apply sqrt_test_false; auto with zarith.
 apply sqrt_main; auto with zarith.
 contradict Hij; apply Zle_not_lt.
 assert ((1 + [|j|]) <= 2 ^ (Z_of_nat size - 1)); auto with zarith.
 apply Zle_trans with ((2 ^ (Z_of_nat size - 1)) ^2); auto with zarith.
 assert (0 <= 1 + [|j|]); auto with zarith.
 apply Zmult_le_compat; auto with zarith.
 change ((2 ^ (Z_of_nat size - 1))^2) with (2 ^ (Z_of_nat size - 2) * wB).
 apply Zle_trans with ([|ih|] * wB); auto with zarith.
 unfold zn2z_to_Z, wB; auto with zarith.
Qed.


Lemma iter2_sqrt_correct n rec ih il j:
  2^(Z_of_nat (size - 2)) <= [|ih|] ->  0 < [|j|] -> [||WW ih il||] < ([|j|] + 1) ^ 2 ->
  (forall j1, 0 < [|j1|] -> 2^(Z_of_nat n) + [|j1|] <= [|j|] ->
      [||WW ih il||] < ([|j1|] + 1) ^ 2 ->
       [|rec ih il j1|] ^ 2 <= [||WW ih il||] < ([|rec ih il j1|] + 1) ^ 2)  ->
  [|iter2_sqrt n rec ih il j|] ^ 2 <= [||WW ih il||]
      < ([|iter2_sqrt n rec ih il j|] + 1) ^ 2.
Proof.
 revert rec ih il j; elim n; unfold iter2_sqrt; fold iter2_sqrt; clear n.
 intros rec ih il j Hi Hj Hij Hrec; apply sqrt2_step_correct; auto with zarith.
 intros; apply Hrec; auto with zarith.
 rewrite Zpower_0_r; auto with zarith.
 intros n Hrec rec ih il j Hi Hj Hij HHrec.
 apply sqrt2_step_correct; auto.
 intros j1 Hj1  Hjp1; apply Hrec; auto with zarith.
 intros j2 Hj2 H2j2 Hjp2; apply Hrec; auto with zarith.
 intros j3 Hj3 Hpj3.
 apply HHrec; auto.
 rewrite inj_S, Zpower_Zsucc.
 apply Zle_trans with (2 ^Z_of_nat n + [|j2|])%Z; auto with zarith.
 apply Zle_0_nat.
Qed.

Lemma sqrt2_spec : forall x y,
       wB/ 4 <= [|x|] ->
       let (s,r) := sqrt2 x y in
          [||WW x y||] = [|s|] ^ 2 + [+|r|] /\
          [+|r|] <= 2 * [|s|].
 Proof.
 intros ih il Hih; unfold sqrt2.
 change [||WW ih il||] with ([||WW ih il||]).
 assert (Hbin: forall s, s * s + 2* s + 1 = (s + 1) ^ 2) by
  (intros s; ring).
 assert (Hb: 0 <= wB) by (red; intros HH; discriminate).
 assert (Hi2: [||WW ih il ||] < ([|max_int|] + 1) ^ 2).
  apply Zle_lt_trans with ((wB - 1) * wB + (wB - 1)); auto with zarith.
  2: apply refl_equal.
  case (to_Z_bounded ih); case (to_Z_bounded il); intros H1 H2 H3 H4.
  unfold zn2z_to_Z; auto with zarith.
 case (iter2_sqrt_correct size (fun _ _ j => j) ih il max_int); auto with zarith.
 apply refl_equal.
 intros j1 _ HH; contradict HH.
 apply Zlt_not_le.
 case (to_Z_bounded j1); auto with zarith.
 change (2 ^ Z_of_nat size) with ([|max_int|]+1)%Z; auto with zarith.
 set (s := iter2_sqrt size (fun _ _ j : int=> j) ih il max_int).
 intros Hs1 Hs2.
 generalize (mulc_spec s s); case mulc.
 simpl fst; simpl snd; intros ih1 il1 Hihl1.
 generalize (subc_spec il il1).
 case subc; intros il2 Hil2.
 simpl interp_carry in Hil2.
 case_eq (ih1  < ih)%int31;  [idtac | rewrite <- not_true_iff_false];
  rewrite ltb_spec; intros Heq.
 unfold interp_carry; rewrite Zmult_1_l.
 rewrite Zpower_2, Hihl1, Hil2.
 case (Zle_lt_or_eq ([|ih1|] + 1) ([|ih|])); auto with zarith.
 intros H2; contradict Hs2; apply Zle_not_lt.
 replace (([|s|] + 1) ^ 2) with ([||WW ih1 il1||] + 2 * [|s|] + 1).
 unfold zn2z_to_Z.
 case (to_Z_bounded il); intros Hpil _.
 assert (Hl1l: [|il1|] <= [|il|]).
  case (to_Z_bounded il2); rewrite Hil2; auto with zarith.
 assert ([|ih1|] * wB + 2 * [|s|] + 1 <= [|ih|] * wB); auto with zarith.
 case (to_Z_bounded s); intros _ Hps.
 case (to_Z_bounded ih1); intros Hpih1 _; auto with zarith.
 apply Zle_trans with (([|ih1|] + 2) * wB); auto with zarith.
 rewrite Zmult_plus_distr_l.
 assert (2 * [|s|] + 1 <= 2 * wB); auto with zarith.
 unfold zn2z_to_Z; rewrite <-Hihl1, Hbin; auto.
 intros H2; split.
 unfold zn2z_to_Z; rewrite <- H2; ring.
 replace (wB + ([|il|] - [|il1|])) with ([||WW ih il||] - ([|s|] * [|s|])).
 rewrite <-Hbin in Hs2; auto with zarith.
 rewrite Hihl1; unfold zn2z_to_Z; rewrite <- H2; ring.
 unfold interp_carry.
 case (Zle_lt_or_eq [|ih|] [|ih1|]); auto with zarith; intros H.
 contradict Hs1.
 apply Zlt_not_le; rewrite Zpower_2, Hihl1.
 unfold zn2z_to_Z.
 case (to_Z_bounded il); intros _ H2.
 apply Zlt_le_trans with (([|ih|] + 1) * wB + 0).
 rewrite Zmult_plus_distr_l, Zplus_0_r; auto with zarith.
 case (to_Z_bounded il1); intros H3 _.
 apply Zplus_le_compat; auto with zarith.
 split.
 rewrite Zpower_2, Hihl1.
 unfold zn2z_to_Z; ring[Hil2 H].
 replace [|il2|] with ([||WW ih il||] - [||WW ih1 il1||]).
 unfold zn2z_to_Z at 2; rewrite <-Hihl1.
 rewrite <-Hbin in Hs2; auto with zarith.
 unfold zn2z_to_Z; rewrite H, Hil2; ring.
 unfold interp_carry in Hil2 |- *.
 assert (Hsih: [|ih - 1|] = [|ih|] - 1).
  rewrite sub_spec, Zmod_small; auto; replace [|1|] with 1; auto.
  case (to_Z_bounded ih); intros H1 H2.
  split; auto with zarith.
  apply Zle_trans with (wB/4 - 1); auto with zarith.
 case_eq (ih1 < ih - 1)%int31;  [idtac | rewrite <- not_true_iff_false];
  rewrite ltb_spec, Hsih; intros Heq.
 rewrite Zpower_2, Hihl1.
 case (Zle_lt_or_eq ([|ih1|] + 2) [|ih|]); auto with zarith.
 intros H2; contradict Hs2; apply Zle_not_lt.
 replace (([|s|] + 1) ^ 2) with ([||WW ih1 il1||] + 2 * [|s|] + 1).
 unfold zn2z_to_Z.
 assert ([|ih1|] * wB + 2 * [|s|] + 1 <= [|ih|] * wB + ([|il|] - [|il1|]));
  auto with zarith.
 rewrite <-Hil2.
 case (to_Z_bounded il2); intros Hpil2 _.
 apply Zle_trans with ([|ih|] * wB + - wB); auto with zarith.
 case (to_Z_bounded s);  intros _ Hps.
 assert (2 * [|s|] + 1 <= 2 * wB); auto with zarith.
 apply Zle_trans with ([|ih1|] * wB + 2 * wB); auto with zarith.
 assert (Hi: ([|ih1|] + 3) * wB <= [|ih|] * wB); auto with zarith.
 rewrite Zmult_plus_distr_l in Hi; auto with zarith.
 unfold zn2z_to_Z; rewrite <-Hihl1, Hbin; auto.
 intros H2; unfold zn2z_to_Z; rewrite <-H2.
 split.
 replace [|il|] with (([|il|] - [|il1|]) + [|il1|]); try ring.
 rewrite <-Hil2; ring.
 replace (1 * wB + [|il2|]) with ([||WW ih il||] - [||WW ih1 il1||]).
 unfold zn2z_to_Z at 2; rewrite <-Hihl1.
 rewrite <-Hbin in Hs2; auto with zarith.
 unfold zn2z_to_Z; rewrite <-H2.
 replace [|il|] with (([|il|] - [|il1|]) + [|il1|]); try ring.
 rewrite <-Hil2; ring.
 case (Zle_lt_or_eq ([|ih|] - 1) ([|ih1|])); auto with zarith; intros H1.
 assert (He: [|ih|] = [|ih1|]).
   apply Zle_antisym; auto with zarith.
   case (Zle_or_lt [|ih1|] [|ih|]); auto; intros H2.
   contradict Hs1; apply Zlt_not_le; rewrite Zpower_2, Hihl1.
  unfold zn2z_to_Z.
  case (to_Z_bounded il); intros _ Hpil1.
  apply Zlt_le_trans with (([|ih|] + 1) * wB).
  rewrite Zmult_plus_distr_l, Zmult_1_l; auto with zarith.
  case (to_Z_bounded il1); intros Hpil2 _.
  apply Zle_trans with (([|ih1|]) * wB); auto with zarith.
 contradict Hs1; apply Zlt_not_le; rewrite Zpower_2, Hihl1.
 unfold zn2z_to_Z; rewrite He.
 assert ([|il|] - [|il1|] < 0); auto with zarith.
 rewrite <-Hil2.
 case (to_Z_bounded il2); auto with zarith.
 split.
 rewrite Zpower_2, Hihl1.
 unfold zn2z_to_Z; rewrite <-H1.
 apply trans_equal with ([|ih|] * wB + [|il1|] + ([|il|] - [|il1|])).
 ring.
 rewrite <-Hil2; ring.
 replace [|il2|] with ([||WW ih il||] - [||WW ih1 il1||]).
 unfold zn2z_to_Z at 2; rewrite <- Hihl1.
 rewrite <-Hbin in Hs2; auto with zarith.
 unfold zn2z_to_Z.
 rewrite <-H1.
 ring_simplify.
 apply trans_equal with (wB + ([|il|] - [|il1|])).
 ring.
 rewrite <-Hil2; ring.
Qed.

Lemma to_Z_gcd : forall i j,
  [|gcd i j|] = Zgcdn (2*size) [|j|] [|i|].
Proof.
 unfold gcd.
 induction (2*size)%nat; intros.
 reflexivity.
 simpl.
 generalize (to_Z_bounded j)(to_Z_bounded i); intros.
 case_eq (j == 0)%int31.
 rewrite eqb_spec;intros H1;rewrite H1.
 replace [|0|] with 0;trivial;rewrite Z.abs_eq;auto with zarith.
 rewrite <- not_true_iff_false, eqb_spec;intros.
 case_eq [|j|]; intros.
 elim H1;apply to_Z_inj;assumption.
 rewrite IHn, <- H2, mod_spec;trivial.
 rewrite H2 in H;destruct H as (H, _);elim H;trivial.
Qed.

Lemma gcd_spec : forall a b, Zis_gcd [|a|] [|b|] [|gcd a b|].
Proof.
 intros.
 rewrite to_Z_gcd.
 apply Zis_gcd_sym.
 apply Zgcdn_is_gcd.
 unfold Zgcd_bound.
 generalize (to_Z_bounded b).
 destruct [|b|].
 unfold size; auto with zarith.
 intros (_,H).
 cut (Psize p <= size)%nat; [ omega | rewrite <- Zpower2_Psize; auto].
 intros (H,_); compute in H; elim H; auto.
Qed.

Lemma head00_spec:  forall x, [|x|] = 0 -> [|head0 x|] = [|digits|].
Proof. 
 change 0 with [|0|];intros x Heq.
 apply to_Z_inj in Heq;rewrite Heq;trivial.
Qed.

Lemma tail00_spec:  forall x, [|x|] = 0 -> [|tail0 x|] = [|digits|].
Proof.
 change 0 with [|0|];intros x Heq.
 apply to_Z_inj in Heq;rewrite Heq;trivial.
Qed.

(* lsr lsl *)
Lemma lsl_0_l i: 0 << i = 0%int31.
Proof.
 apply to_Z_inj.
 generalize (lsl_spec 0 i).
 rewrite to_Z_0, Zmult_0_l, Zmod_0_l; auto.
Qed.

Lemma lsl_0_r i: i << 0 = i.
Proof.
 apply to_Z_inj.
 rewrite lsl_spec, to_Z_0, Zmult_1_r.
 apply Zmod_small; apply (to_Z_bounded i).
Qed.

Lemma lsl_M_r x i (H: (digits <= i = true)%int31) : x << i = 0%int31.
Proof.
 apply to_Z_inj.
 rewrite lsl_spec, to_Z_0.
 rewrite leb_spec in H.
 unfold wB; change (Z_of_nat size) with [|digits|].
 replace ([|i|]) with (([|i|] - [|digits|]) + [|digits|])%Z; try ring.
 rewrite Zpower_exp, Zmult_assoc, Z_mod_mult; auto with arith.
 apply Zle_ge; auto with zarith.
 case (to_Z_bounded digits); auto with zarith.
Qed.

Lemma lsr_0_l i: 0 >> i = 0%int31.
Proof.
 apply to_Z_inj.
 generalize (lsr_spec 0 i).
 rewrite to_Z_0, Zdiv_0_l; auto.
Qed.

Lemma lsr_0_r i: i >> 0 = i.
Proof.
 apply to_Z_inj.
 rewrite lsr_spec, to_Z_0, Zdiv_1_r; auto.
Qed.

Lemma lsr_M_r x i (H: (digits <= i = true)%int31) : x >> i = 0%int31.
Proof.
 apply to_Z_inj.
 rewrite lsr_spec, to_Z_0.
 case (to_Z_bounded x); intros H1x H2x.
 case (to_Z_bounded digits); intros H1d H2d.
 rewrite leb_spec in H.
 apply Zdiv_small; split; auto.
 apply Zlt_le_trans with (1 := H2x).
 unfold wB; change (Z_of_nat size) with [|digits|].
 apply Zpower_le_monotone; auto with zarith.
Qed.

Lemma add_le_r m n: 
  if  (n <= m + n)%int31 then  ([|m|] + [|n|] < wB)%Z else  (wB <= [|m|] + [|n|])%Z.
Proof.
 case (to_Z_bounded m); intros H1m H2m.
 case (to_Z_bounded n); intros H1n H2n.
 case (Zle_or_lt wB ([|m|] + [|n|])); intros H.
   assert (H1: ([| m + n |] = [|m|] + [|n|] - wB)%Z).
     rewrite add_spec.
     replace (([|m|] + [|n|]) mod wB)%Z with (((([|m|] + [|n|]) - wB) + wB) mod wB)%Z.
     rewrite Zplus_mod, Z_mod_same_full, Zplus_0_r, !Zmod_small; auto with zarith.
     rewrite !Zmod_small; auto with zarith.
     apply f_equal2 with (f := Zmod); auto with zarith.
   case_eq (n <= m + n)%int31; auto.
   rewrite leb_spec, H1; auto with zarith.
 assert (H1: ([| m + n |] = [|m|] + [|n|])%Z).
   rewrite add_spec, Zmod_small; auto with zarith.
 replace (n <= m + n)%int31 with true; auto.
 apply sym_equal; rewrite leb_spec, H1; auto with zarith.
Qed.

Lemma lsr_add i m n: ((i >> m) >> n = if n <= m + n then i >> (m + n) else 0)%int31.
Proof.
 case (to_Z_bounded m); intros H1m H2m.
 case (to_Z_bounded n); intros H1n H2n.
 case (to_Z_bounded i); intros H1i H2i.
 generalize (add_le_r m n); case (n <= m + n)%int31; intros H.
   apply to_Z_inj; rewrite !lsr_spec, Zdiv_Zdiv, <- Zpower_exp; auto with zarith.
   rewrite add_spec, Zmod_small; auto with zarith.
 apply to_Z_inj; rewrite !lsr_spec, Zdiv_Zdiv, <- Zpower_exp; auto with zarith.
 apply Zdiv_small; split; auto with zarith.
 apply Zlt_le_trans with (1 := H2i).
 apply Zle_trans with (1 := H).
 apply Zpower2_le_lin; auto with zarith.
Qed.

Lemma lsl_add i m n: ((i << m) << n = if n <= m + n then i << (m + n) else 0)%int31.
Proof.
 case (to_Z_bounded m); intros H1m H2m.
 case (to_Z_bounded n); intros H1n H2n.
 case (to_Z_bounded i); intros H1i H2i.
 generalize (add_le_r m n); case (n <= m + n)%int31; intros H.
   apply to_Z_inj; rewrite !lsl_spec, Zmult_mod, Zmod_mod, <- Zmult_mod.
   rewrite <-Zmult_assoc, <- Zpower_exp; auto with zarith.
   apply f_equal2 with (f := Zmod); auto.
   rewrite add_spec, Zmod_small; auto with zarith.
 apply to_Z_inj; rewrite !lsl_spec, Zmult_mod, Zmod_mod, <- Zmult_mod.
 rewrite <-Zmult_assoc, <- Zpower_exp; auto with zarith.
 unfold wB.
 replace ([|m|] + [|n|])%Z with 
         ((([|m|] + [|n|]) - Z_of_nat size) + Z_of_nat size)%Z.
 2: ring.
 rewrite Zpower_exp, Zmult_assoc, Z_mod_mult; auto with zarith.
 assert (Z_of_nat size < wB)%Z; auto with zarith.
 apply Zpower2_lt_lin; auto with zarith.
Qed.

Coercion b2i (b: bool) : int := if b then 1%int31 else 0%int31.

Lemma bit_0 n : bit 0 n = false.
Proof. unfold bit; rewrite lsr_0_l; auto. Qed.

Lemma lsr_1 n : 1 >> n = (n == 0).
Proof.
 case_eq (n == 0).
 rewrite eqb_spec; intros H; rewrite H, lsr_0_r.
 apply refl_equal.
 intros Hn.
 assert (H1n : (1 >> n = 0)%int31); auto.
 apply to_Z_inj; rewrite lsr_spec.
 apply Zdiv_small; rewrite to_Z_1; split; auto with zarith.
 change 1%Z with (2^0)%Z.
 apply Zpower_lt_monotone; split; auto with zarith.
 case (Zle_lt_or_eq  0 [|n|]); auto.
 case (to_Z_bounded n); auto.
 intros H1.
 assert ((n == 0) = true).
 rewrite eqb_spec; apply to_Z_inj; rewrite <-H1, to_Z_0; auto.
 generalize H; rewrite Hn; discriminate.
Qed.

Lemma bit_1 n : bit 1 n = (n == 0).
Proof.
 unfold bit; rewrite lsr_1.
 case (n == 0).
 apply refl_equal.
 rewrite lsl_0_l; apply refl_equal.
Qed.

Lemma bit_M i n (H: (digits <= n = true)%int31): bit i n = false.
Proof. unfold bit; rewrite lsr_M_r; auto. Qed.

Lemma bit_half i n (H: (n < digits = true)%int31) : bit (i>>1) n = bit i (n+1).
Proof.
 unfold bit.
 rewrite lsr_add.
 case_eq (n <= (1 + n))%int31.
 replace (1+n)%int31 with (n+1)%int31; [auto|idtac].
 apply to_Z_inj; rewrite !add_spec, Zplus_comm; auto.
 intros H1; assert (H2: n = max_int).
 2: generalize H; rewrite H2; discriminate.
 case (to_Z_bounded n); intros H1n H2n.
 case (Zle_lt_or_eq [|n|] (wB - 1)); auto with zarith; 
   intros H2; apply to_Z_inj; auto.
 generalize (add_le_r 1 n); rewrite H1.
 change [|max_int|] with (wB - 1)%Z.
 replace [|1|] with 1%Z; auto with zarith.
Qed.

Lemma bit_0_spec i: [|bit i 0|] = [|i|] mod 2.
Proof.
 unfold bit, is_zero; rewrite lsr_0_r.
 assert (Hbi: ([|i|] mod 2 < 2)%Z).
   apply Z_mod_lt; auto with zarith.
 case (to_Z_bounded i); intros H1i H2i.
 case (Zmod_le_first [|i|] 2); auto with zarith; intros H3i H4i.
 assert (H2b: (0 < 2 ^ [|digits - 1|])%Z).
   apply Zpower_gt_0; auto with zarith.
   case (to_Z_bounded (digits -1)); auto with zarith.
 assert (H: [|i << (digits -1)|] = ([|i|] mod 2 * 2^ [|digits -1|])%Z).
 rewrite lsl_spec.
 rewrite (Z_div_mod_eq [|i|] 2) at 1; auto with zarith.
 rewrite Zmult_plus_distr_l, <-Zplus_mod_idemp_l.
 rewrite (Zmult_comm 2), <-Zmult_assoc.
 replace (2 * 2 ^ [|digits - 1|])%Z with wB; auto.
 rewrite Z_mod_mult, Zplus_0_l; apply Zmod_small.
 split; auto with zarith.
 replace wB with (2 * 2 ^ [|digits -1|])%Z; auto.
 apply Zmult_lt_compat_r; auto with zarith.
 case (Zle_lt_or_eq 0 ([|i|] mod 2)); auto with zarith; intros Hi.
 2: generalize H; rewrite <-Hi, Zmult_0_l.
 2: replace 0%Z with [|0|]; auto.
 2: rewrite to_Z_eq, <-eqb_spec; intros H1; rewrite H1; auto.
 generalize H; replace ([|i|] mod 2) with 1%Z; auto with zarith.
 rewrite Zmult_1_l.
 intros H1.
 assert (H2: [|i << (digits - 1)|] <> [|0|]).
  replace [|0|] with 0%Z; auto with zarith.
 generalize (eqb_spec (i << (digits - 1)) 0).
 case (i << (digits - 1) == 0); auto.
 intros (H3,_); case H2.
 rewrite to_Z_eq; auto.
Qed.

Lemma bit_split i : (i = (i>>1)<<1 + bit i 0)%int31.
Proof.
 apply to_Z_inj.
 rewrite add_spec, lsl_spec, lsr_spec, bit_0_spec, Zplus_mod_idemp_l.
 replace (2 ^ [|1|]) with 2%Z; auto with zarith.
 rewrite Zmult_comm, <-Z_div_mod_eq; auto with zarith.
 rewrite Zmod_small; auto; case (to_Z_bounded i); auto.
Qed.

Lemma bit_eq i1 i2:
  i1 = i2 <-> forall i, bit i1 i = bit i2 i.
Proof.
 split; try (intros; subst; auto; fail).
 case (to_Z_bounded i2); case (to_Z_bounded i1).
 unfold wB; generalize i1 i2; elim size; clear i1 i2.
 replace (2^Z_of_nat 0) with 1%Z; auto with zarith.
 intros; apply to_Z_inj; auto with zarith.
 intros n IH i1 i2 H1i1 H2i1 H1i2 H2i2 H.
 rewrite (bit_split i1), (bit_split i2).
 rewrite H.
 apply f_equal2 with (f := add); auto.
 apply f_equal2 with (f := lsl); auto.
 apply IH; try rewrite lsr_spec;
   replace (2^[|1|]) with 2%Z;  auto with zarith.
 apply Zdiv_lt_upper_bound; auto with zarith.
 generalize H2i1; rewrite inj_S.
 unfold Zsucc; rewrite Zpower_exp; auto with zarith.
 apply Zdiv_lt_upper_bound; auto with zarith.
 generalize H2i2; rewrite inj_S.
 unfold Zsucc; rewrite Zpower_exp; auto with zarith.
 intros i.
 case (Zle_or_lt [|digits|] [|i|]); intros Hi.
 rewrite !bit_M; auto; rewrite leb_spec; auto.
 rewrite !bit_half; auto; rewrite ltb_spec; auto with zarith.
Qed.

Lemma bit_lsr x i j :
 (bit (x >> i) j = if j <= i + j then bit x (i + j) else false)%int31.
Proof.
 unfold bit; rewrite lsr_add; case leb; auto.
Qed.

Lemma bit_lsl x i j : bit (x << i) j = 
(if (j < i) || (digits <= j) then false else bit x (j - i))%int31.
Proof.
 assert (F1: 1 >= 0) by discriminate.
 case_eq (digits <= j)%int31; intros H.
 rewrite orb_true_r, bit_M; auto.
 set (d := [|digits|]).
 case (Zle_or_lt d [|j|]); intros H1.
 case (leb_spec digits j); rewrite H; auto with zarith.
 intros _ HH; generalize (HH H1); discriminate.
 clear H.
 generalize (ltb_spec j i); case ltb; intros H2; unfold bit; simpl.
 assert (F2: ([|j|] < [|i|])%Z) by (case H2; auto); clear H2.
 replace (is_zero (((x << i) >> j) << (digits - 1))) with true; auto.
 case (to_Z_bounded j); intros  H1j H2j.
 apply sym_equal; rewrite is_zero_spec; apply to_Z_inj.
 rewrite lsl_spec, lsr_spec, lsl_spec.
 replace wB with (2^d); auto.
 pattern d at 1; replace d with ((d - ([|j|] + 1)) + ([|j|] + 1))%Z.
 2: ring.
 rewrite Zpower_exp; auto with zarith.
 replace [|i|] with (([|i|] - ([|j|] + 1)) + ([|j|] + 1))%Z.
 2: ring.
 rewrite Zpower_exp, Zmult_assoc; auto with zarith.
 rewrite Zmult_mod_distr_r.
 rewrite Zplus_comm, Zpower_exp, !Zmult_assoc; auto with zarith.
 rewrite Z_div_mult_full; auto with zarith.
 2: assert (0 < 2 ^ [|j|])%Z; auto with zarith.
 rewrite <-Zmult_assoc, <-Zpower_exp; auto with zarith.
 replace (1 + [|digits - 1|])%Z with d; auto with zarith.
 rewrite Z_mod_mult; auto.
 case H2; intros _ H3; case (Zle_or_lt [|i|] [|j|]); intros F2.
 2: generalize (H3 F2); discriminate.
 clear H2 H3.
 apply f_equal with (f := negb).
 apply f_equal with (f := is_zero).
 apply to_Z_inj.
 rewrite !lsl_spec, !lsr_spec, !lsl_spec.
 pattern wB at 2 3; replace wB with (2^(1+ [|digits - 1|])); auto.
 rewrite Zpower_exp, Zpower_1_r; auto with zarith.
 rewrite !Zmult_mod_distr_r.
 apply f_equal2 with (f := Zmult); auto.
 replace wB with (2^ d); auto with zarith.
 replace d with ((d - [|i|]) + [|i|])%Z.
 2: ring.
 case (to_Z_bounded i); intros  H1i H2i.
 rewrite Zpower_exp; auto with zarith.
 rewrite Zmult_mod_distr_r.
 case (to_Z_bounded j); intros  H1j H2j.
 replace [|j - i|] with ([|j|] - [|i|])%Z.
 2: rewrite sub_spec, Zmod_small; auto with zarith.
 set (d1 := (d - [|i|])%Z).
 set (d2 := ([|j|] - [|i|])%Z).
 pattern [|j|] at 1; 
   replace [|j|] with (d2 + [|i|])%Z.
 2: unfold d2; ring.
 rewrite Zpower_exp; auto with zarith.
 rewrite Zdiv_mult_cancel_r; auto with zarith.
 2: unfold d2; auto with zarith.
 rewrite (Z_div_mod_eq [|x|] (2^d1)) at 2; auto with zarith.
 2: apply Zlt_gt; apply Zpower_gt_0; unfold d1; auto with zarith.
 pattern d1 at 2; 
   replace d1 with (d2 + (1+ (d - [|j|] - 1)))%Z.
 2: unfold d1, d2; ring.
 rewrite Zpower_exp; auto with zarith.
 2: unfold d2; auto with zarith.
 rewrite <-Zmult_assoc, Zmult_comm.
 rewrite Z_div_plus_l; auto with zarith.
 2: unfold d2; auto with zarith.
 rewrite Zpower_exp, Zpower_1_r; auto with zarith.
 rewrite <-Zplus_mod_idemp_l.
 rewrite <-!Zmult_assoc, Zmult_comm, Z_mod_mult, Zplus_0_l; auto.
Qed.

Lemma bit_b2i (b: bool) i : bit b i = (i == 0) && b.
Proof.
 case b; unfold bit; simpl b2i.
 2: rewrite lsr_0_l, lsl_0_l, andb_false_r; auto.
 rewrite lsr_1; case (i == 0); auto.
Qed.

Lemma bit_or_split i : (i = (i>>1)<<1 lor bit i 0)%int31.
Proof.
 rewrite bit_eq.
 intros n; rewrite lor_spec.
 rewrite bit_lsl, bit_lsr, bit_b2i.
 case (to_Z_bounded n); intros Hi _.
 case (Zle_lt_or_eq _ _ Hi).
 2: replace 0%Z with [|0|]; auto; rewrite to_Z_eq.
 2: intros H; rewrite <-H.
 2: replace (0 < 1)%int31 with true; auto.
 intros H; clear Hi.
 case_eq (n == 0).
 rewrite eqb_spec; intros H1; generalize H; rewrite H1; discriminate.
 intros _; rewrite orb_false_r.
 case_eq (n < 1)%int31.
 rewrite ltb_spec, to_Z_1; intros HH; contradict HH; auto with zarith.
 intros _.
 generalize (@bit_M i n); case leb.
 intros H1; rewrite H1; auto.
 intros _.
 case (to_Z_bounded n); intros H1n H2n.
 assert (F1: [|n - 1|] = ([|n|] - 1)%Z).
 rewrite sub_spec, Zmod_small; rewrite to_Z_1; auto with zarith.
 generalize (add_le_r 1 (n - 1)); case leb; rewrite F1, to_Z_1; intros HH.
 replace (1 + (n -1))%int31 with n; auto.
 apply to_Z_inj; rewrite add_spec, F1, Zmod_small; rewrite to_Z_1;
  auto with zarith.
 rewrite bit_M; auto; rewrite leb_spec.
 replace [|n|] with wB; try discriminate; auto with zarith.
Qed.

(* is_zero *)
Lemma is_zero_0: is_zero 0 = true.
Proof. apply refl_equal. Qed.

(* is_even *)
Lemma is_even_bit i : is_even i = negb (bit i 0).
Proof.
 unfold is_even.
 replace (i land 1) with (b2i (bit i 0)).
 case bit; auto.
 apply bit_eq; intros n.
 rewrite bit_b2i, land_spec, bit_1.
 generalize (eqb_spec n 0).
 case (n == 0); auto.
 intros(H,_); rewrite andb_true_r, H; auto.
 rewrite andb_false_r; auto.
Qed.

Lemma is_even_0: is_even 0 = true.
Proof. apply refl_equal. Qed.

Lemma is_even_lsl_1 i: is_even (i << 1) = true.
Proof.
 rewrite is_even_bit, bit_lsl; auto.
Qed.

Lemma is_even_spec : forall x,
      if is_even x then [|x|] mod 2 = 0 else [|x|] mod 2 = 1.
Proof.
intros x; rewrite is_even_bit.
generalize (bit_0_spec x); case bit; simpl; auto.
Qed.

(* More land *)

Lemma land_0_l i: 0 land i = 0%int31.
Proof.
 apply bit_eq; intros n.
 rewrite land_spec, bit_0; auto.
Qed.

Lemma land_0_r i: i land 0 = 0%int31.
Proof.
 apply bit_eq; intros n.
 rewrite land_spec, bit_0, andb_false_r; auto.
Qed.

Lemma land_assoc i1 i2 i3 :
  i1 land (i2 land i3) = i1 land i2 land i3.
Proof.
 apply bit_eq; intros n.
 rewrite !land_spec, andb_assoc; auto.
Qed.

Lemma land_comm i j : i land j = j land i.
Proof.
 apply bit_eq; intros n.
 rewrite !land_spec, andb_comm; auto.
Qed.

Lemma lor_comm i1 i2 : i1 lor i2 = i2 lor i1.
Proof.
 apply bit_eq; intros n.
 rewrite !lor_spec, orb_comm; auto.
Qed.

Lemma lor_assoc i1 i2 i3 :
  i1 lor (i2 lor i3) = i1 lor i2 lor i3.
Proof.
 apply bit_eq; intros n.
 rewrite !lor_spec, orb_assoc; auto.
Qed.

Lemma land_lor_distrib_r i1 i2 i3 :
 i1 land (i2 lor i3) = (i1 land i2) lor (i1 land i3).
Proof.
 apply bit_eq; intros n.
 rewrite !land_spec, !lor_spec, !land_spec, andb_orb_distrib_r; auto.
Qed.

Lemma land_lor_distrib_l i1 i2 i3 :
 (i1 lor i2) land i3 = (i1 land i3) lor (i2 land i3).
Proof.
 apply bit_eq; intros n.
 rewrite !land_spec, !lor_spec, !land_spec, andb_orb_distrib_l; auto.
Qed.

Lemma lor_land_distrib_r i1 i2 i3:
  i1 lor (i2 land i3) = (i1 lor i2) land (i1 lor i3).
Proof.
 apply bit_eq; intros n.
 rewrite !land_spec, !lor_spec, !land_spec, orb_andb_distrib_r; auto.
Qed.

Lemma lor_land_distrib_l i1 i2 i3:
  (i1 land i2) lor i3 = (i1 lor i3) land (i2 lor i3).
Proof.
 apply bit_eq; intros n.
 rewrite !land_spec, !lor_spec, !land_spec, orb_andb_distrib_l; auto.
Qed.

Lemma absoption_land i1 i2 : i1 land (i1 lor i2) = i1.
Proof.
 apply bit_eq; intros n.
 rewrite land_spec, lor_spec, absoption_andb; auto.
Qed.

Lemma absoption_lor i1 i2: i1 lor (i1 land i2) = i1.
Proof.
 apply bit_eq; intros n.
 rewrite lor_spec, land_spec, absoption_orb; auto.
Qed.

Lemma land_lsl i1 i2 i: (i1 land i2) << i = (i1 << i) land (i2 << i).
Proof.
 apply bit_eq; intros n.
 rewrite land_spec, !bit_lsl, land_spec.
 case (_ || _); auto.
Qed.

Lemma lor_lsl i1 i2 i: (i1 lor i2) << i = (i1 << i) lor (i2 << i).
Proof.
 apply bit_eq; intros n.
 rewrite lor_spec, !bit_lsl, lor_spec.
 case (_ || _); auto.
Qed.

Lemma lxor_lsl i1 i2 i: (i1 lxor i2) << i = (i1 << i) lxor (i2 << i).
Proof.
 apply bit_eq; intros n.
 rewrite lxor_spec, !bit_lsl, lxor_spec.
 case (_ || _); auto.
Qed.

Lemma land_lsr i1 i2 i: (i1 land i2) >> i = (i1 >> i) land (i2 >> i).
Proof.
 apply bit_eq; intros n.
 rewrite land_spec, !bit_lsr, land_spec.
 case (_ <= _)%int31; auto.
Qed.

Lemma lor_lsr i1 i2 i: (i1 lor i2) >> i = (i1 >> i) lor (i2 >> i).
Proof.
 apply bit_eq; intros n.
 rewrite lor_spec, !bit_lsr, lor_spec.
 case (_ <= _)%int31; auto.
Qed.

Lemma lxor_lsr i1 i2 i: (i1 lxor i2) >> i = (i1 >> i) lxor (i2 >> i).
Proof.
 apply bit_eq; intros n.
 rewrite lxor_spec, !bit_lsr, lxor_spec.
 case (_ <= _)%int31; auto.
Qed.

Lemma is_even_and i j : is_even (i land j) = is_even i || is_even j.
Proof.
 rewrite !is_even_bit, land_spec; case bit; auto.
Qed.

Lemma is_even_or i j : is_even (i lor j) = is_even i && is_even j.
Proof.
 rewrite !is_even_bit, lor_spec; case bit; auto.
Qed.

Lemma is_even_xor i j : is_even (i lxor j) = negb (xorb (is_even i) (is_even j)).
Proof.
 rewrite !is_even_bit, lxor_spec; do 2 case bit; auto.
Qed.

Lemma lsl_add_distr x y n: (x + y) << n = ((x << n) + (y << n))%int31.
Proof.
 apply to_Z_inj; rewrite !lsl_spec, !add_spec, Zmult_mod_idemp_l.
 rewrite !lsl_spec, <-Zplus_mod.
 apply f_equal2 with (f := Zmod); auto with zarith.
Qed.

Lemma add_assoc x y z: (x + (y + z) = (x + y) + z)%int31.
Proof.
 apply to_Z_inj; rewrite !add_spec.
 rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r, Zplus_assoc; auto.
Qed.

Lemma add_comm x y: (x + y = y + x)%int31.
Proof.
 apply to_Z_inj; rewrite !add_spec, Zplus_comm; auto.
Qed.

Lemma lsr_add_distr x y n: (x + y) << n = ((x << n) + (y << n))%int31.
Proof.
 apply to_Z_inj.
 rewrite add_spec, !lsl_spec, add_spec.
 rewrite Zmult_mod_idemp_l, <-Zplus_mod.
 apply f_equal2 with (f := Zmod); auto with zarith.
Qed.

Lemma is_even_add x y : 
  is_even (x + y) = negb (xorb (negb (is_even x)) (negb (is_even y))).
Proof.
 assert (F : [|x + y|] mod 2 = ([|x|] mod 2 + [|y|] mod 2) mod 2).
  assert (F1: (2 | wB)) by (apply Zpower_divide; apply refl_equal).
  assert (F2: 0 < wB) by (apply refl_equal).
  case (to_Z_bounded x); intros H1x H2x.
  case (to_Z_bounded y); intros H1y H2y.
  rewrite add_spec, <-Zmod_div_mod; auto with zarith.
  rewrite (Z_div_mod_eq [|x|] 2) at 1; auto with zarith.
  rewrite (Z_div_mod_eq [|y|] 2) at 1; auto with zarith.
  rewrite Zplus_mod.
  rewrite Zmult_comm, (fun x => Zplus_comm (x * 2)), Z_mod_plus; auto with zarith.
  rewrite Zmult_comm, (fun x => Zplus_comm (x * 2)), Z_mod_plus; auto with zarith.
  rewrite !Zmod_mod, <-Zplus_mod; auto.
 generalize (is_even_spec (x + y)) (is_even_spec x) (is_even_spec y).
 do 3 case is_even; auto; rewrite F; intros H1 H2 H3;
  generalize H1; rewrite H2, H3; try discriminate.
Qed.

Lemma bit_add_0 x y: bit (x + y) 0 = xorb (bit x 0) (bit y 0).
Proof.
 rewrite <-(fun x => (negb_involutive (bit x 0))).
 rewrite <-is_even_bit, is_even_add, !is_even_bit.
 do 2 case bit; auto.
Qed.
 
Lemma add_cancel_l x y z : (x + y = x + z)%int31 -> y = z.
Proof.
 intros H; case (to_Z_bounded x); case (to_Z_bounded y); case (to_Z_bounded z); 
  intros H1z H2z H1y H2y H1x H2x.
 generalize (add_le_r y x) (add_le_r z x); rewrite (add_comm y x), H, (add_comm z x).
 case_eq  (x <= x + z)%int31; intros H1 H2 H3.
 apply to_Z_inj; generalize H; rewrite <-to_Z_eq, !add_spec, !Zmod_small; auto with zarith.
 apply to_Z_inj; assert ([|x|] + [|y|] = [|x|] + [|z|]); auto with zarith.
 assert (F1: wB > 0) by apply refl_equal.
 rewrite (Z_div_mod_eq ([|x|] + [|y|]) wB), (Z_div_mod_eq ([|x|] + [|z|]) wB); auto.
 rewrite <-to_Z_eq, !add_spec in H; rewrite H.
 replace (([|x|] + [|y|])/wB) with 1.
 replace (([|x|] + [|z|])/wB) with 1; auto with zarith.
 apply Zle_antisym.
 apply Zdiv_le_lower_bound; auto with zarith.
 assert (F2: [|x|] + [|z|] < 2 * wB); auto with zarith.
 generalize (Zdiv_lt_upper_bound _ _ _ (Zgt_lt _ _ F1) F2); auto with zarith.
 apply Zle_antisym.
 apply Zdiv_le_lower_bound; auto with zarith.
 assert (F2: [|x|] + [|y|] < 2 * wB); auto with zarith.
 generalize (Zdiv_lt_upper_bound _ _ _ (Zgt_lt _ _ F1) F2); auto with zarith.
Qed.

Lemma add_cancel_r x y z : (y + x = z + x)%int31 -> y = z.
Proof.
  rewrite !(fun t => add_comm t x); intros Hl; apply (add_cancel_l x); auto.
Qed.

Lemma to_Z_split x : [|x|] = [|(x  >> 1)|] * 2 + [|bit x 0|].
Proof.
  case (to_Z_bounded x); intros H1x H2x.
  case (to_Z_bounded (bit x 0)); intros H1b H2b.
  assert (F1: 0 <= [|x >> 1|] < wB/2).
    rewrite lsr_spec, to_Z_1, Zpower_1_r; split; auto with zarith.
    apply Zdiv_lt_upper_bound; auto with zarith.
  rewrite (bit_split x) at 1.
  rewrite add_spec, Zmod_small, lsl_spec, to_Z_1, Zpower_1_r, Zmod_small; 
    split; auto with zarith.
  change wB with ((wB/2)*2); auto with zarith.
  rewrite lsl_spec, to_Z_1, Zpower_1_r, Zmod_small; auto with zarith.
  change wB with ((wB/2)*2); auto with zarith.
  rewrite lsl_spec, to_Z_1, Zpower_1_r, Zmod_small; auto with zarith.
  2: change wB with ((wB/2)*2); auto with zarith.
  change wB with (((wB/2 - 1) * 2 + 1) + 1).
  assert ([|bit x 0|] <= 1); auto with zarith.
  case bit; discriminate.
Qed.

Lemma lor_le x y : (y <= x lor y)%int31 = true.
Proof.
 generalize x y (to_Z_bounded x) (to_Z_bounded y); clear x y.
 unfold wB; elim size.
 replace (2^Z_of_nat 0) with 1%Z; auto with zarith.
 intros x y Hx Hy; replace x with 0%int31.
 replace y with 0%int31; auto.
 apply to_Z_inj; rewrite to_Z_0; auto with zarith.
 apply to_Z_inj; rewrite to_Z_0; auto with zarith.
 intros n IH x y; rewrite inj_S.
 unfold Zsucc; rewrite Zpower_exp, Zpower_1_r; auto with zarith.
 intros Hx Hy.
 rewrite leb_spec.
 rewrite (to_Z_split y) at 1; rewrite (to_Z_split (x lor y)).
 assert ([|y>>1|] <= [|(x lor y) >> 1|]).
  rewrite lor_lsr, <-leb_spec; apply IH.
  rewrite lsr_spec, to_Z_1, Zpower_1_r; split; auto with zarith.
  apply Zdiv_lt_upper_bound; auto with zarith.
  rewrite lsr_spec, to_Z_1, Zpower_1_r; split; auto with zarith.
  apply Zdiv_lt_upper_bound; auto with zarith.
 assert ([|bit y 0|] <= [|bit (x lor y) 0|]); auto with zarith.
 rewrite lor_spec; do 2 case bit; try discriminate.
Qed.


Lemma bit_add_or x y: 
  (forall n, bit x n = true -> bit y n = true -> False) <-> (x + y)%int31= x lor y.
Proof.
 generalize x y (to_Z_bounded x) (to_Z_bounded y); clear x y.
 unfold wB; elim size.
 replace (2^Z_of_nat 0) with 1%Z; auto with zarith.
 intros x y Hx Hy; replace x with 0%int31.
 replace y with 0%int31.
 split; auto; intros _ n; rewrite !bit_0; discriminate.
 apply to_Z_inj; rewrite to_Z_0; auto with zarith.
 apply to_Z_inj; rewrite to_Z_0; auto with zarith.
 intros n IH x y; rewrite inj_S.
 unfold Zsucc; rewrite Zpower_exp, Zpower_1_r; auto with zarith.
 intros Hx Hy.
 split.
 intros Hn.
 assert (F1: ((x >> 1) + (y >> 1))%int31 = (x >> 1) lor (y >> 1)).
   apply IH.
   rewrite lsr_spec, Zpower_1_r; split; auto with zarith.
   apply Zdiv_lt_upper_bound; auto with zarith.
   rewrite lsr_spec, Zpower_1_r; split; auto with zarith.
   apply Zdiv_lt_upper_bound; auto with zarith.
   intros m H1 H2.
   case_eq (digits <= m)%int31;  [idtac | rewrite <- not_true_iff_false];
     intros Heq.
   rewrite bit_M in H1; auto; discriminate.
   rewrite leb_spec in Heq.
   apply (Hn (m + 1)%int31);
     rewrite <-bit_half; auto; rewrite ltb_spec; auto with zarith.
 rewrite (bit_split (x lor y)), lor_lsr, <- F1, lor_spec.
 replace (b2i (bit x 0 || bit y 0)) with (bit x 0 + bit y 0)%int31.
 2: generalize (Hn 0%int31); do 2 case bit; auto; intros []; auto.
 rewrite lsl_add_distr.
 rewrite (bit_split x) at 1; rewrite (bit_split y) at 1.
 rewrite <-!add_assoc; apply f_equal2 with (f := add); auto.
 rewrite add_comm, <-!add_assoc; apply f_equal2 with (f := add); auto.
 rewrite add_comm; auto.
 intros Heq.
 generalize (add_le_r x y); rewrite Heq, lor_le; intro Hb.
 generalize Heq; rewrite (bit_split x) at 1; rewrite (bit_split y )at 1; clear Heq.
 rewrite (fun y => add_comm y (bit x 0)), <-!add_assoc, add_comm,
         <-!add_assoc, (add_comm (bit y 0)), add_assoc, <-lsr_add_distr.
 rewrite (bit_split (x lor y)), lor_spec.
 intros Heq.
 assert (F: (bit x 0 + bit y 0)%int31 = (bit x 0 || bit y 0)).
  assert (F1: (2 | wB)) by (apply Zpower_divide; apply refl_equal).
  assert (F2: 0 < wB) by (apply refl_equal).
  assert (F3: [|bit x  0 + bit y 0|] mod 2 = [|bit x 0 || bit y 0|] mod 2).
  apply trans_equal with (([|(x>>1 + y>>1) << 1|] + [|bit x 0 + bit y 0|]) mod 2).
  rewrite lsl_spec, Zplus_mod, <-Zmod_div_mod; auto with zarith.
  rewrite Zpower_1_r, Z_mod_mult, Zplus_0_l, Zmod_mod; auto with zarith.
  rewrite (Zmod_div_mod 2 wB), <-add_spec, Heq; auto with zarith.
  rewrite add_spec, <-Zmod_div_mod; auto with zarith.
  rewrite lsl_spec, Zplus_mod, <-Zmod_div_mod; auto with zarith.
  rewrite Zpower_1_r, Z_mod_mult, Zplus_0_l, Zmod_mod; auto with zarith.
  generalize F3; do 2 case bit; try discriminate; auto.
 case (IH (x >> 1) (y >> 1)).
 rewrite lsr_spec, to_Z_1, Zpower_1_r; split; auto with zarith.
 apply Zdiv_lt_upper_bound; auto with zarith.
 rewrite lsr_spec, to_Z_1, Zpower_1_r; split; auto with zarith.
 apply Zdiv_lt_upper_bound; auto with zarith.
 intros _ HH m; case (to_Z_bounded m); intros H1m H2m.
 case_eq (digits <= m)%int31.
 intros Hlm; rewrite bit_M; auto; discriminate.
 rewrite <- not_true_iff_false, leb_spec; intros Hlm.
 case (Zle_lt_or_eq 0 [|m|]); auto; intros Hm.
 replace m with ((m -1) + 1)%int31.
 rewrite <-(bit_half x), <-(bit_half y); auto with zarith.
 apply HH.
 rewrite <-lor_lsr.
 assert (0 <= [|bit (x lor y) 0|] <= 1) by (case bit; split; discriminate).
 rewrite F in Heq; generalize (add_cancel_r _ _ _ Heq).
 intros Heq1; apply to_Z_inj.
 generalize Heq1; rewrite <-to_Z_eq, lsl_spec, to_Z_1, Zpower_1_r, Zmod_small.
 rewrite lsl_spec, to_Z_1, Zpower_1_r, Zmod_small; auto with zarith.
 case (to_Z_bounded (x lor y)); intros H1xy H2xy.
 rewrite lsr_spec, to_Z_1, Zpower_1_r; auto with zarith.
 change wB with ((wB/2)*2); split; auto with zarith.
 assert ([|x lor y|] / 2  < wB / 2); auto with zarith.
 apply Zdiv_lt_upper_bound; auto with zarith.
 split.
 case (to_Z_bounded (x >> 1 + y >> 1)); auto with zarith.
 rewrite add_spec.
 apply Zle_lt_trans with (([|x >> 1|] + [|y >> 1|]) * 2); auto with zarith.
 case (Zmod_le_first ([|x >> 1|] + [|y >> 1|]) wB); auto with zarith.
 case (to_Z_bounded (x >> 1)); case (to_Z_bounded (y >> 1)); auto with zarith.
 generalize Hb; rewrite (to_Z_split x) at 1; rewrite (to_Z_split y) at 1.
 case (to_Z_bounded (bit x 0)); case (to_Z_bounded (bit y 0)); auto with zarith.
 rewrite ltb_spec, sub_spec, to_Z_1, Zmod_small; auto with zarith.
 rewrite ltb_spec, sub_spec, to_Z_1, Zmod_small; auto with zarith.
 apply to_Z_inj.
 rewrite add_spec, sub_spec, Zplus_mod_idemp_l, to_Z_1, Zmod_small; auto with zarith.
 replace m with 0%int31.
 intros Hbx Hby; generalize F; rewrite <-to_Z_eq, Hbx, Hby; discriminate.
 apply to_Z_inj; auto.
Qed.

Lemma addmuldiv_spec : forall x y p, [|p|] <= [|digits|] ->
   [| addmuldiv p x y |] =
   ([|x|] * (2 ^ [|p|]) + [|y|] / (2 ^ ([|digits|] - [|p|]))) mod wB.
Proof.
 intros x y p H.
 assert (Fp := to_Z_bounded p); assert (Fd := to_Z_bounded digits).
 rewrite addmuldiv_def_spec; unfold addmuldiv_def.
 case (bit_add_or (x << p) (y >> (digits - p))); intros HH _.
 rewrite <-HH, add_spec, lsl_spec, lsr_spec, Zplus_mod_idemp_l, sub_spec.
 rewrite (fun x y => Zmod_small (x - y)); auto with zarith.
 intros n; rewrite bit_lsl, bit_lsr.
 generalize (add_le_r (digits - p) n).
 case leb; try discriminate.
 rewrite sub_spec, Zmod_small; auto with zarith; intros H1.
 case_eq (n < p)%int31; try discriminate.
 rewrite <- not_true_iff_false, ltb_spec; intros H2.
 case leb; try discriminate.
 intros _; rewrite bit_M; try discriminate.
 rewrite leb_spec, add_spec, Zmod_small, sub_spec, Zmod_small; auto with zarith.
 rewrite sub_spec, Zmod_small; auto with zarith.
Qed. 

Lemma lxor_comm: forall i1 i2 : int, i1 lxor i2 = i2 lxor i1.
Proof.
 intros;apply bit_eq;intros.
 rewrite !lxor_spec;apply xorb_comm.
Qed.

Lemma lxor_assoc: forall i1 i2 i3 : int, i1 lxor (i2 lxor i3) = i1 lxor i2 lxor i3.
Proof.
 intros;apply bit_eq;intros.
 rewrite !lxor_spec, xorb_assoc;trivial.
Qed.

Lemma lxor_0_l : forall i, 0 lxor i = i.
Proof.
  intros;apply bit_eq;intros.
  rewrite lxor_spec, bit_0, xorb_false_l;trivial.
Qed.

Lemma lxor_0_r : forall i, i lxor 0 = i.
Proof.
 intros;rewrite lxor_comm;apply lxor_0_l.
Qed.

Lemma lxor_nilpotent: forall i, i lxor i = 0%int31.
Proof.
 intros;apply bit_eq;intros.
 rewrite lxor_spec, xorb_nilpotent, bit_0;trivial.
Qed.

Lemma lor_0_l : forall i, 0 lor i = i.
Proof.
  intros;apply bit_eq;intros.
  rewrite lor_spec, bit_0, orb_false_l;trivial.
Qed.

Lemma lor_0_r : forall i, i lor 0 = i.
Proof.
 intros;rewrite lor_comm;apply lor_0_l.
Qed.

Lemma reflect_leb : forall i j, reflect ([|i|] <= [|j|])%Z (i <= j)%int31.
Proof.
 intros; apply iff_reflect.
 symmetry;apply leb_spec.
Qed.

Lemma reflect_eqb : forall i j, reflect (i = j)%Z (i == j).
Proof.
 intros; apply iff_reflect.
 symmetry;apply eqb_spec.
Qed.

Lemma reflect_ltb : forall i j, reflect ([|i|] < [|j|])%Z (i < j)%int31.
Proof.
 intros; apply iff_reflect.
 symmetry;apply ltb_spec.
Qed.

Lemma lsr_is_even_eq : forall i j,
  i >> 1 = j >> 1 ->
  is_even i = is_even j ->
  i = j.
Proof.
 intros;apply bit_eq.
 intros n;destruct (reflect_eqb n 0).
 rewrite <- (negb_involutive (bit i n)), <- (negb_involutive (bit j n)).
 rewrite e, <- !is_even_bit, H0;trivial.
 assert (W1 : [|n|] <> 0) by (intros Heq;apply n0;apply to_Z_inj;trivial).
 assert (W2 := to_Z_bounded n);clear n0.
 assert (W3 : [|n-1|] = [|n|] - 1).
   rewrite sub_spec, to_Z_1, Zmod_small;trivial;omega.
 assert (H1 : n = ((n-1)+1)%int31).
   apply to_Z_inj;rewrite add_spec, W3.
   rewrite Zmod_small;rewrite to_Z_1; omega.
 destruct (reflect_ltb (n-1) digits).
  rewrite <- ltb_spec in z.
  rewrite H1, <- !bit_half, H;trivial.
 assert ((digits <= n)%int31 = true).
  rewrite leb_spec;omega.
 rewrite !bit_M;trivial.
Qed.

Lemma lsr1_bit : forall i k, (bit i k >> 1 = 0)%int31.
Proof.
 intros;destruct (bit i k);trivial.
Qed.

Lemma bit_xor_split: forall i : int, i = (i >> 1) << 1 lxor bit i 0.
Proof.
 intros.
 rewrite bit_or_split at 1.
 apply lsr_is_even_eq.
 rewrite lxor_lsr, lor_lsr, lsr1_bit, lxor_0_r, lor_0_r;trivial.
 rewrite is_even_or, is_even_xor.
 rewrite is_even_lsl_1;trivial.
 rewrite (xorb_true_l (is_even (bit i 0))), negb_involutive;trivial.
Qed.

(** Order *)
Local Open Scope int31_scope.

Lemma succ_max_int : forall x,
  (x < max_int)%int31 = true -> (0 < x + 1)%int31 = true.
Proof.
 intros x;rewrite ltb_spec, ltb_spec, add_spec.
 intros; assert (W:= to_Z_bounded x); assert (W1:= to_Z_bounded max_int).
 change [|0|] with 0%Z;change [|1|] with 1%Z.
 rewrite Zmod_small;omega.
Qed.

Lemma leb_max_int : forall x, (x <= max_int)%int31 = true.
Proof.
 intros x;rewrite leb_spec;assert (W:= to_Z_bounded x).
 change [|max_int|] with (wB - 1)%Z;omega.
Qed.

Lemma leb_0 : forall x, 0 <= x = true.
Proof.
 intros x;rewrite leb_spec;destruct (to_Z_bounded x);trivial.
Qed.

Lemma ltb_0 : forall x, ~ (x < 0 = true).
Proof.
 intros x;rewrite ltb_spec, to_Z_0;destruct (to_Z_bounded x);omega.
Qed.

Lemma leb_trans : forall x y z, x <= y = true ->  y <= z = true -> x <= z = true.
Proof.
 intros x y z;rewrite !leb_spec;apply Zle_trans.
Qed.

Lemma ltb_trans : forall x y z, x < y = true ->  y < z = true -> x < z = true.
Proof.
 intros x y z;rewrite !ltb_spec;apply Zlt_trans.
Qed.

Lemma ltb_leb_trans : forall x y z, x < y = true ->  y <= z = true -> x < z = true.
Proof.
 intros x y z;rewrite leb_spec, !ltb_spec;apply Zlt_le_trans.
Qed.

Lemma leb_ltb_trans : forall x y z, x <= y = true ->  y < z = true -> x < z = true.
Proof.
 intros x y z;rewrite leb_spec, !ltb_spec;apply Zle_lt_trans.
Qed.

Lemma gtb_not_leb : forall n m, m < n = true -> ~(n <= m = true).
Proof.
 intros n m; rewrite ltb_spec, leb_spec;omega.
Qed.

Lemma leb_not_gtb : forall n m, m <= n = true -> ~(n < m = true).
Proof.
 intros n m; rewrite ltb_spec, leb_spec;omega.
Qed.

Lemma leb_refl : forall n, n <= n = true.
Proof.
 intros n;rewrite leb_spec;apply Zle_refl.
Qed.

Lemma leb_negb_gtb : forall x y, x <= y = negb (y < x).
Proof.
 intros x y;apply Bool.eq_true_iff_eq;split;intros.
 apply Bool.eq_true_not_negb;apply leb_not_gtb;trivial.
 rewrite Bool.negb_true_iff, <- Bool.not_true_iff_false in H.
 rewrite leb_spec; rewrite ltb_spec in H;omega.
Qed.

Lemma ltb_negb_geb : forall x y, x < y = negb (y <= x).
Proof.
 intros;rewrite leb_negb_gtb, Bool.negb_involutive;trivial.
Qed.

Lemma to_Z_sub_gt : forall x y, y <= x = true -> [|x - y|] = ([|x|] - [|y|])%Z.
Proof.
 intros x y;assert (W:= to_Z_bounded x);assert (W0:= to_Z_bounded y);
   rewrite leb_spec;intros;rewrite sub_spec, Zmod_small;omega.
Qed.
 
Lemma not_0_ltb : forall x, x <> 0 <-> 0 < x = true.
Proof.
 intros x;rewrite ltb_spec, to_Z_0;assert (W:=to_Z_bounded x);split.
 intros Hd;assert ([|x|] <> 0)%Z;[ | omega].
   intros Heq;elim Hd;apply to_Z_inj;trivial.
 intros Hlt Heq;elimtype False.
 assert ([|x|] = 0)%Z;[ rewrite Heq, to_Z_0;trivial | omega].
Qed.

Lemma not_ltb_refl : forall i, ~(i < i = true).
Proof.
 intros;rewrite ltb_spec;omega.
Qed.

Lemma to_Z_sub_1 : forall x y, y < x = true -> ([| x - 1|] = [|x|] - 1)%Z.
Proof.
 intros;apply to_Z_sub_gt.
 generalize (leb_ltb_trans _ _ _ (leb_0 y) H).
 rewrite ltb_spec, leb_spec, to_Z_0, to_Z_1;auto with zarith.
Qed.
 
Lemma to_Z_sub_1_diff : forall x, x <> 0 -> ([| x - 1|] = [|x|] - 1)%Z.
Proof.
  intros x;rewrite not_0_ltb;apply to_Z_sub_1.
Qed.

Lemma to_Z_add_1 : forall x y, x < y = true -> [|x+1|] = ([|x|] + 1)%Z.
Proof.
  intros x y;assert (W:= to_Z_bounded x);assert (W0:= to_Z_bounded y);
   rewrite ltb_spec;intros;rewrite add_spec, to_Z_1, Zmod_small;omega.
Qed.
 
Lemma ltb_leb_sub1 : forall x i,  x <> 0 -> (i < x = true <-> i <= x - 1 = true).
Proof.
 intros x i Hdiff.
 rewrite ltb_spec, leb_spec, to_Z_sub_1_diff;trivial.
 split;auto with zarith.
Qed.

Lemma ltb_leb_add1 : forall x y i, i < y = true -> (i < x = true <-> i + 1 <= x = true).
Proof.
 intros x y i Hlt.
 rewrite ltb_spec, leb_spec.
 rewrite (to_Z_add_1 i y);trivial.
 split;auto with zarith.
Qed.

(** Iterators *)

Lemma foldi_gt : forall A f from to (a:A), 
  (to < from)%int31 = true -> foldi f from to a = a.
Proof.
 intros;unfold foldi;rewrite foldi_cont_gt;trivial.
Qed.

Lemma foldi_eq : forall A f from to (a:A),
  from = to -> foldi f from to a = f from a.
Proof.
 intros;unfold foldi;rewrite foldi_cont_eq;trivial.
Qed.

Lemma foldi_lt : forall A f from to (a:A), 
  (from < to)%int31 = true -> foldi f from to a = foldi f (from + 1) to (f from a).
Proof.
 intros;unfold foldi;rewrite foldi_cont_lt;trivial.
Qed.

Lemma fold_gt : forall A f from to (a:A), 
  (to < from)%int31 = true -> fold f from to a = a.
Proof.
 intros;apply foldi_gt;trivial.
Qed.

Lemma fold_eq : forall A f from to (a:A),
  from = to -> fold f from to a = f a.
Proof.
 intros;apply foldi_eq;trivial.
Qed.

Lemma fold_lt : forall A f from to (a:A), 
  (from < to)%int31 = true -> fold f from to a = fold f (from + 1) to (f a).
Proof.
 intros;apply foldi_lt;trivial.
Qed.

Lemma foldi_down_lt : forall A f from downto (a:A),
  (from < downto)%int31 = true -> foldi_down f from downto a = a.
Proof.
 intros;unfold foldi_down;rewrite foldi_down_cont_lt;trivial.
Qed.

Lemma foldi_down_eq : forall A f from downto (a:A),
  from = downto -> foldi_down f from downto a = f from a.
Proof.
 intros;unfold foldi_down;rewrite foldi_down_cont_eq;trivial.
Qed.

Lemma foldi_down_gt : forall A f from downto (a:A),
  (downto < from)%int31 = true-> 
  foldi_down f from downto a = 
  foldi_down f (from-1) downto (f from a).
Proof.
 intros;unfold foldi_down;rewrite foldi_down_cont_gt;trivial.
Qed.

Lemma fold_down_lt : forall A f from downto (a:A),
  (from < downto)%int31 = true -> fold_down f from downto a = a.
Proof.
 intros;apply foldi_down_lt;trivial.
Qed.

Lemma fold_down_eq : forall A f from downto (a:A),
  from = downto -> fold_down f from downto a = f a.
Proof.
 intros;apply foldi_down_eq;trivial.
Qed.

Lemma fold_down_gt : forall A f from downto (a:A),
  (downto < from)%int31 = true-> 
  fold_down f from downto a = 
  fold_down f (from-1) downto (f a).
Proof.
 intros;apply foldi_down_gt;trivial.
Qed.

Require Import Wf_Z.

Lemma int_ind : forall (P:int -> Type),
  P 0%int31 ->
  (forall i, (i < max_int)%int31 = true -> P i -> P (i + 1)%int31) ->
  forall i, P i.
Proof.
 intros P HP0 Hrec.
 assert (forall z, (0 <= z)%Z -> forall i, z = [|i|] -> P i).
 intros z H;pattern z;apply natlike_rec2;intros;trivial.
 rewrite <- (of_to_Z i), <- H0;exact HP0.
 assert (W:= to_Z_bounded i).
 assert ([|i - 1|] = [|i|] - 1)%Z.
  rewrite sub_spec, Zmod_small;rewrite to_Z_1;auto with zarith.
 assert (i = i - 1 + 1)%int31.
  apply to_Z_inj.
  rewrite add_spec, H2.
  rewrite Zmod_small;rewrite to_Z_1;auto with zarith.
 rewrite H3;apply Hrec.
 rewrite ltb_spec, H2;change [|max_int|] with (wB - 1)%Z;auto with zarith.
 apply X;auto with zarith.
 intros;apply (X [|i|]);trivial.
 destruct (to_Z_bounded i);trivial.
Qed.
 
Lemma int_ind_bounded : forall (P:int-> Type) min max,
  min <= max =true ->
  P max ->
  (forall i, min <= i + 1 = true-> i < max =true-> P (i + 1) -> P i) ->
  P min.
Proof.
 intros P min max Hle.
 intros Hmax Hrec.
 assert (W1:= to_Z_bounded max);assert (W2:= to_Z_bounded min).
 assert (forall z, (0 <= z)%Z -> (z <= [|max|] - [|min|])%Z  -> forall i, z = [|i|] -> P (max - i)%int31).
 intros z H1;pattern z;apply natlike_rec2;intros;trivial.
 assert (max - i = max)%int31.
  apply to_Z_inj;rewrite sub_spec, <- H0, Zminus_0_r, Zmod_small;auto using to_Z_bounded.
 rewrite H2;trivial.
 assert (W3:= to_Z_bounded i);apply Hrec.
 rewrite leb_spec,add_spec, sub_spec, to_Z_1, (Zmod_small ([|max|] - [|i|])), Zmod_small;auto with zarith.
 rewrite ltb_spec, sub_spec, Zmod_small;auto with zarith.
 assert (max - i + 1 = max - (i - 1))%int31.
  apply to_Z_inj;rewrite add_spec, !sub_spec, to_Z_1.
  rewrite (Zmod_small ([|max|] - [|i|]));auto with zarith.
  rewrite (Zmod_small ([|i|] - 1));auto with zarith.
  apply f_equal2;auto with zarith.
 rewrite H3;apply X;auto with zarith.
 rewrite sub_spec, to_Z_1, <- H2, Zmod_small;auto with zarith.
 rewrite leb_spec in Hle;assert (min = max - (max - min))%int31.
  apply to_Z_inj.
  rewrite !sub_spec, !Zmod_small;auto with zarith.
  rewrite Zmod_small;auto with zarith.
 rewrite H;apply (X [| max - min |]);trivial;rewrite sub_spec, Zmod_small;auto with zarith.
Qed.

Lemma foldi_cont_ZInd : forall A B (P: Z -> (A -> B) -> Prop) (f:int -> (A -> B) -> (A -> B)) min max cont,
   (forall z, ([|max|] < z)%Z -> P z cont) ->
   (forall i cont, min <= i = true -> i <= max = true -> P ([|i|] + 1)%Z cont -> P [|i|] (f i cont)) ->
   P [|min|] (foldi_cont f min max cont).
Proof.
 intros A B P f min max cont Ha Hf.
 assert (Bmax:= to_Z_bounded max);assert (Bmin:= to_Z_bounded min).
 case_eq (min <= max);intros Heq.
 generalize (leb_refl min).
 assert (P ([|max|] + 1)%Z cont) by (apply Ha;auto with zarith).
 clear Ha;revert cont H.
 pattern min at 2 3 4;apply int_ind_bounded with max;trivial.
 intros;rewrite foldi_cont_eq;auto using leb_refl.
 intros i Hle Hlt Hr cont Hcont Hle'.
 rewrite foldi_cont_lt;[ | trivial].
 apply Hf;trivial. rewrite leb_spec;rewrite ltb_spec in Hlt;auto with zarith.
 assert ([|i|] + 1 = [|i + 1|])%Z.
  rewrite ltb_spec in Hlt;assert (W:= to_Z_bounded i);rewrite add_spec, to_Z_1, Zmod_small;omega.
 rewrite H;apply Hr;trivial.
 assert (max < min = true) by (rewrite ltb_negb_geb,Heq;trivial).
 rewrite foldi_cont_gt;trivial;apply Ha;rewrite <- ltb_spec;trivial.
Qed.

Lemma of_pos_spec : forall p, [|of_pos p|] = Zpos p mod wB. 
Proof.
Admitted.

Lemma of_Z_spec : forall z, [|of_Z z|] = z mod wB.
Proof.
 assert (W:= to_Z_bounded 0).
 unfold of_Z;destruct z.
 rewrite Zmod_small;trivial.
 apply of_pos_spec.
 rewrite opp_spec, of_pos_spec.
Admitted.

Lemma foldi_cont_Ind : forall A B (P: int -> (A -> B) -> Prop) (f:int -> (A -> B) -> (A -> B)) min max cont,
   max < max_int = true ->
   (forall z, max < z = true -> P z cont) ->
   (forall i cont, min <= i = true -> i <= max = true -> P (i + 1) cont -> P i (f i cont)) ->
   P min (foldi_cont f min max cont).
Proof.
 intros.
 set (P' z cont := (0 <= z < wB)%Z -> P (of_Z z) cont).
 assert (P' [|min|] (foldi_cont f min max cont)).
 apply foldi_cont_ZInd;unfold P';intros.
 assert ([|(of_Z z)|] = z).
  rewrite of_Z_spec, Zmod_small;trivial.
 apply H0;rewrite ltb_spec, H4;trivial.
 rewrite of_to_Z;apply H1;trivial.
 assert (i < max_int = true).
   apply leb_ltb_trans with max;trivial.
 rewrite <- (to_Z_add_1 _ _ H6), of_to_Z in H4;apply H4.
 apply to_Z_bounded.
 unfold P' in H2;rewrite of_to_Z in H2;apply H2;apply to_Z_bounded.
Qed.

Lemma foldi_cont_ind : forall A B (P: (A -> B) -> Prop) (f:int -> (A -> B) -> (A -> B)) min max cont,
   P cont ->
   (forall i cont, min <= i = true -> i <= max = true -> P cont -> P (f i cont)) ->
   P (foldi_cont f min max cont).
Proof.
 intros A B P f min max cont Ha Hf.
 set (P2 := fun (z:Z) b => P b);change (P2 [|min|] (foldi_cont f min max cont)).
 apply foldi_cont_ZInd;trivial.
Qed.

Lemma foldi_ZInd : forall A (P : Z -> A -> Prop) f min max a,  
  (max < min = true -> P ([|max|] + 1)%Z a) ->
  P [|min|] a ->
  (forall i a, min <= i = true -> i <= max = true -> 
      P [|i|] a -> P ([|i|] + 1)%Z (f i a)) ->
  P ([|max|]+1)%Z (foldi f min max a).
Proof.
 unfold foldi;intros A P f min max a Hlt;intros.
 set (P' z cont := 
       if Zlt_bool [|max|] z then cont = (fun a0 : A => a0)
       else forall a, P z a -> P ([|max|]+1)%Z (cont a)).
 assert (P' [|min|] (foldi_cont (fun (i : int) (cont : A -> A) (a0 : A) => cont (f i a0)) min
                       max (fun a0 : A => a0))).
 apply foldi_cont_ZInd;intros;red.
 rewrite Zlt_is_lt_bool in H1;rewrite H1;trivial.
 case_eq (Zlt_bool [|max|] [|i|]);intros.
  rewrite <- Zlt_is_lt_bool in H4;rewrite leb_spec in H2;elimtype False;omega.
 clear H4; revert H3;unfold P'.
 case_eq (Zlt_bool [|max|] ([|i|] + 1));intros;auto.
  rewrite <- Zlt_is_lt_bool in H3; assert ([|i|] = [|max|]) by (rewrite leb_spec in H2;omega).
  rewrite H4, <- H6;apply H0;trivial.
 revert H1;unfold P'.
 case_eq (Zlt_bool [|max|] [|min|]);auto.
 rewrite <- Zlt_is_lt_bool, <- ltb_spec;intros;rewrite foldi_cont_gt;auto.
Qed.

Lemma foldi_Ind : forall A (P : int -> A -> Prop) f min max a,  
  (max < max_int = true) ->
  (max < min = true -> P (max + 1) a) ->
  P min a ->
  (forall i a, min <= i = true -> i <= max = true -> 
      P i a -> P (i + 1) (f i a)) ->
  P (max+1) (foldi f min max a).
Proof.
 intros.
 set (P' z a := (0 <= z < wB)%Z -> P (of_Z z) a).
 assert (W:= to_Z_add_1 _ _ H). 
 assert (P' ([|max|]+1)%Z (foldi f min max a)).
 apply foldi_ZInd;unfold P';intros.
 rewrite <- W, of_to_Z;auto.
 rewrite of_to_Z;trivial.
 assert (i < max_int = true).
   apply leb_ltb_trans with max;trivial.
 rewrite <- (to_Z_add_1 _ _ H7), of_to_Z;apply H2;trivial.
 rewrite of_to_Z in H5;apply H5;apply to_Z_bounded.
 unfold P' in H3;rewrite <- W, of_to_Z in H3;apply H3;apply to_Z_bounded.
Qed.

Lemma foldi_ind : forall A (P: A -> Prop) (f:int -> A -> A) min max a,
   P a ->
   (forall i a, min <= i = true -> i <= max = true -> P a -> P (f i a)) ->
   P (foldi f min max a).
Proof.
 unfold foldi;intros A P f min max a Ha Hr;revert a Ha.
 apply foldi_cont_ind;auto.
Qed.

Lemma fold_ind : forall A (P: A -> Prop) (f: A -> A) min max a,
   P a -> (forall a, P a -> P (f a)) -> P (fold f min max a).
Proof.
 unfold fold;intros A P f min max a Ha Hr;revert a Ha.
 apply foldi_cont_ind;auto.
Qed.

Lemma foldi_down_cont_ZInd :
   forall A B (P: Z -> (A -> B) -> Prop) (f:int -> (A -> B) -> (A -> B)) max min cont,
   (forall z, (z < [|min|])%Z -> P z cont) -> 
   (forall i cont, min <= i = true -> i <= max = true -> P ([|i|] - 1)%Z cont -> P [|i|] (f i cont)) ->
   P [|max|] (foldi_down_cont f max min cont).
Proof.
 intros A B P f max min cont Ha Hf.
 assert (Bmax:= to_Z_bounded max);assert (Bmin:= to_Z_bounded min).
 case_eq (min <= max);intros Heq.
 generalize (leb_refl max).
 assert (P ([|min|] -1)%Z cont) by (apply Ha;auto with zarith).
 clear Ha;revert cont H Heq.
 pattern max at 1 2 4 5;apply int_ind;trivial.
 intros; assert (0 = min).
   apply to_Z_inj;revert Heq;rewrite leb_spec, to_Z_0;omega.
 rewrite foldi_down_cont_eq;subst;auto.
 intros i Hmaxi Hr cont Hcont Hmin Hmax.
 generalize Hmin;rewrite leb_ltb_eqb;case_eq (min < i+1);simpl;intros Hlt Hmin'.
 rewrite foldi_down_cont_gt;[ | trivial].
 apply Hf;trivial.
 assert ([|i|] + 1 = [|i + 1|])%Z.
   assert (W:= to_Z_bounded i);rewrite ltb_spec in Hmaxi;
    assert (W2 := to_Z_bounded max_int);rewrite add_spec, to_Z_1, Zmod_small;auto with zarith.
 assert (i + 1 - 1 = i).
  rewrite leb_spec in *;rewrite ltb_spec in *.
  assert (W1:= to_Z_bounded i); apply to_Z_inj;rewrite sub_spec,to_Z_1, Zmod_small;try omega.
 assert ([|i|] = [|i+1|]-1)%Z.
   rewrite <- H;ring.
 rewrite <- H1, H0;apply Hr;trivial.
 rewrite ltb_spec in Hlt;rewrite leb_spec;omega.
 rewrite leb_spec in Hmax |- *;omega.
 rewrite eqb_spec in Hmin';subst;rewrite foldi_down_cont_eq;auto.
 assert (max < min = true) by (rewrite ltb_negb_geb,Heq;trivial).
 rewrite foldi_down_cont_lt;trivial.
 apply Ha;rewrite <- ltb_spec;trivial.
Qed.

Lemma foldi_down_cont_ind : forall A B (P: (A -> B) -> Prop) (f:int -> (A -> B) -> (A -> B)) max min cont,
   P cont ->
   (forall i cont, min <= i = true -> i <= max = true -> P cont -> P (f i cont)) ->
   P (foldi_down_cont f max min cont).
Proof.
 intros A B P f max min cont Ha Hf.
 set (P2 := fun (z:Z) b => P b);change (P2 [|max|] (foldi_down_cont f max min cont)).
 apply foldi_down_cont_ZInd;trivial.
Qed.

Lemma foldi_down_ZInd :
   forall A (P: Z -> A -> Prop) (f:int -> A -> A) max min a,
   (max < min = true -> P ([|min|] - 1)%Z a) ->
   (P [|max|] a) -> 
   (forall i a, min <= i = true -> i <= max = true -> P [|i|]%Z a -> P ([|i|]-1)%Z (f i a)) ->
   P ([|min|] - 1)%Z (foldi_down f max min a).
Proof.
 unfold foldi_down;intros A P f max min a Hlt;intros.
 set (P' z cont := 
       if Zlt_bool z [|min|] then cont = (fun a0 : A => a0)
       else forall a, P z a -> P ([|min|] - 1)%Z (cont a)).
 assert (P' [|max|] (foldi_down_cont (fun (i : int) (cont : A -> A) (a0 : A) => cont (f i a0)) max
                       min (fun a0 : A => a0))).
 apply foldi_down_cont_ZInd;intros;red.
 rewrite Zlt_is_lt_bool in H1;rewrite H1;trivial.
 case_eq (Zlt_bool [|i|] [|min|]);intros.
  rewrite <- Zlt_is_lt_bool in H4;rewrite leb_spec in H1;elimtype False;omega.
 clear H4;revert H3;unfold P'.
 case_eq (Zlt_bool ([|i|] - 1) [|min|]);intros;auto.
  rewrite <- Zlt_is_lt_bool in H3; assert ([|i|] = [|min|]) by (rewrite leb_spec in H1;omega).
  rewrite H4, <- H6. apply H0;trivial.
 revert H1;unfold P'.
 case_eq (Zlt_bool [|max|] [|min|]);auto.
 rewrite <- Zlt_is_lt_bool, <- ltb_spec;intros;rewrite foldi_down_cont_lt;auto.
Qed.

Lemma foldi_down_ind : forall A (P: A -> Prop) (f:int -> A -> A) max min a,
   P a ->
   (forall i a, min <= i = true -> i <= max = true -> P a -> P (f i a)) ->
   P (foldi_down f max min a).
Proof.
 unfold foldi_down;intros A P f max min a Ha Hr;revert a Ha.
 apply foldi_down_cont_ind;auto.
Qed.

Lemma fold_down_ind : forall A (P: A -> Prop) (f: A -> A) max min a,
   P a -> (forall a, P a -> P (f a)) -> P (fold_down f max min a).
Proof.
 unfold fold_down;intros A P f max min a Ha Hr;revert a Ha.
 apply foldi_down_cont_ind;auto.
Qed.

Lemma foldi_cont_ZInd2 : forall A B (P: Z -> (A -> B) -> (A -> B) -> Prop) (f1 f2:int -> (A -> B) -> (A -> B)) min max cont1 cont2,
   (forall z, ([|max|] < z)%Z -> P z cont1 cont2) ->
   (forall i cont1 cont2, min <= i = true -> i <= max = true -> P ([|i|] + 1)%Z cont1 cont2 -> 
                               P [|i|] (f1 i cont1) (f2 i cont2)) ->
   P [|min|] (foldi_cont f1 min max cont1) (foldi_cont f2 min max cont2).
Proof.
 intros.
 set (P' z cont := 
        if Zlt_bool [|max|] z then cont = cont1
        else P z cont (foldi_cont f2 (of_Z z) max cont2)).
 assert (P' [|min|] (foldi_cont f1 min max cont1)).
  apply foldi_cont_ZInd;unfold P';intros.
  rewrite Zlt_is_lt_bool in H1;rewrite H1;trivial.
  case_eq (Zlt_bool [|max|] [|i|]);intros.
  rewrite <- Zlt_is_lt_bool, <- ltb_spec in H4.
  elim (not_ltb_refl max);apply ltb_leb_trans with i;trivial.
  rewrite of_to_Z;generalize H2;rewrite leb_ltb_eqb, orb_true_iff;intros [Hlt | Heq].
  rewrite foldi_cont_lt;[apply H0 | ];trivial.
  revert H3;case_eq (Zlt_bool [|max|] ([|i|] + 1)).
  rewrite <- Zlt_is_lt_bool;rewrite ltb_spec in Hlt;intros;elimtype False;omega.
  rewrite <- (to_Z_add_1 _ _ Hlt), of_to_Z; intros _ W;exact W.
  rewrite eqb_spec in Heq;subst.
  rewrite foldi_cont_eq;[apply H0 | ];trivial.
  assert ([|max|] < [|max|] + 1)%Z by auto with zarith.
   rewrite Zlt_is_lt_bool in H5;rewrite H5 in H3;rewrite H3.
   apply H;rewrite Zlt_is_lt_bool;trivial.
 revert H1;unfold P';case_eq (Zlt_bool [|max|] [|min|]).
 rewrite <- Zlt_is_lt_bool;intros.
 rewrite H2;rewrite foldi_cont_gt;[ | rewrite ltb_spec];auto.
 rewrite of_to_Z;auto.
Qed.

Lemma foldi_ZInd2 : forall A (P : Z -> A -> A -> Prop) f1 f2 min max a1 a2,  
  (max < min = true -> P ([|max|] + 1)%Z a1 a2) ->
  P [|min|] a1 a2 ->
  (forall i a1 a2, min <= i = true -> i <= max = true -> 
      P [|i|] a1 a2 -> P ([|i|] + 1)%Z (f1 i a1) (f2 i a2)) ->
  P ([|max|]+1)%Z (foldi f1 min max a1) (foldi f2 min max a2).
Proof.
 unfold foldi;intros A P f1 f2 min max a1 a2 Hlt;intros.
 set (P' z cont1 cont2 := 
       if Zlt_bool [|max|] z then cont1 = (fun a0 : A => a0) /\ cont2 = (fun a0 : A => a0)
       else forall a1 a2, P z a1 a2 -> P ([|max|]+1)%Z (cont1 a1) (cont2 a2)).
 assert (P' [|min|] (foldi_cont (fun (i : int) (cont : A -> A) (a0 : A) => cont (f1 i a0)) min
                       max (fun a0 : A => a0)) 
                    (foldi_cont (fun (i : int) (cont : A -> A) (a0 : A) => cont (f2 i a0)) min
                       max (fun a0 : A => a0))).
 apply foldi_cont_ZInd2;intros;red.
 rewrite Zlt_is_lt_bool in H1;rewrite H1;auto.
 case_eq (Zlt_bool [|max|] [|i|]);intros.
  rewrite <- Zlt_is_lt_bool in H4;rewrite leb_spec in H2;elimtype False;omega.
 clear H4; revert H3;unfold P'.
 case_eq (Zlt_bool [|max|] ([|i|] + 1));intros;auto.
  rewrite <- Zlt_is_lt_bool in H3; assert ([|i|] = [|max|]) by (rewrite leb_spec in H2;omega).
  destruct H4;subst;rewrite <- H6;apply H0;trivial.
 revert H1;unfold P'.
 case_eq (Zlt_bool [|max|] [|min|]);auto.
 rewrite <- Zlt_is_lt_bool, <- ltb_spec;intros;rewrite !foldi_cont_gt;auto.
Qed.

Lemma foldi_eq_compat : forall A (f1 f2:int -> A -> A) min max a,
  (forall i a, min <= i = true -> i <= max = true -> f1 i a = f2 i a) ->
  foldi f1 min max a = foldi f2 min max a.
Proof.
 intros; set (P' (z:Z) (a1 a2:A) := a1 = a2).
 assert (P' ([|max|] + 1)%Z (foldi f1 min max a) (foldi f2 min max a)).
 apply foldi_ZInd2;unfold P';intros;subst;auto.
 apply H0.
Qed.

Lemma foldi_down_cont_ZInd2 :
   forall A B (P: Z -> (A -> B) -> (A -> B) -> Prop) (f1 f2:int -> (A -> B) -> (A -> B)) max min cont1 cont2,
   (forall z, (z < [|min|])%Z -> P z cont1 cont2) -> 
   (forall i cont1 cont2, min <= i = true -> i <= max = true -> P ([|i|] - 1)%Z cont1 cont2 ->
             P [|i|] (f1 i cont1) (f2 i cont2)) ->
   P [|max|] (foldi_down_cont f1 max min cont1) (foldi_down_cont f2 max min cont2).
Proof.
  intros.
 set (P' z cont := 
        if Zlt_bool z [|min|] then cont = cont1 
        else P z cont (foldi_down_cont f2 (of_Z z) min cont2)).
 assert (P' [|max|] (foldi_down_cont f1 max min cont1)).
  apply foldi_down_cont_ZInd;unfold P';intros.
  rewrite Zlt_is_lt_bool in H1;rewrite H1;trivial.
  case_eq (Zlt_bool [|i|] [|min|]);intros.
  rewrite <- Zlt_is_lt_bool, <- ltb_spec in H4.
  elim (not_ltb_refl min);apply leb_ltb_trans with i;trivial.
  rewrite of_to_Z;generalize H1;rewrite leb_ltb_eqb, orb_true_iff;intros [Hlt | Heq].
  rewrite foldi_down_cont_gt;[apply H0 | ];trivial.
  revert H3;case_eq (Zlt_bool ([|i|] - 1) [|min|]).
  rewrite <- Zlt_is_lt_bool;rewrite ltb_spec in Hlt;intros;elimtype False;omega.
  rewrite <- (to_Z_sub_1 _ _ Hlt), of_to_Z; intros _ W;exact W.
  rewrite eqb_spec in Heq;subst.
  rewrite foldi_down_cont_eq;[apply H0 | ];trivial.
  assert ([|i|] - 1 < [|i|])%Z by auto with zarith.
   rewrite Zlt_is_lt_bool in H5;rewrite H5 in H3;rewrite H3.
   apply H;rewrite Zlt_is_lt_bool;trivial.
 revert H1;unfold P';case_eq (Zlt_bool [|max|] [|min|]).
 rewrite <- Zlt_is_lt_bool;intros.
 rewrite H2;rewrite foldi_down_cont_lt;[ | rewrite ltb_spec];auto.
 rewrite of_to_Z;auto.
Qed.

Lemma foldi_down_ZInd2 :
   forall A (P: Z -> A -> A -> Prop) (f1 f2:int -> A -> A) max min a1 a2,
   (max < min = true -> P ([|min|] - 1)%Z a1 a2) ->
   (P [|max|] a1 a2) -> 
   (forall z, (z < [|min|])%Z -> P z a1 a2) -> 
   (forall i a1 a2, min <= i = true -> i <= max = true -> P [|i|] a1 a2 ->
             P ([|i|] - 1)%Z (f1 i a1) (f2 i a2)) ->
   P ([|min|] - 1)%Z (foldi_down f1 max min a1) (foldi_down f2 max min a2).
Proof.
 unfold foldi_down;intros A P f1 f2 max min a1 a2 Hlt;intros.
 set (P' z cont1 cont2 := 
       if Zlt_bool z [|min|] then cont1 = (fun a0 : A => a0) /\ cont2 = (fun a0 : A => a0)
       else forall a1 a2, P z a1 a2 -> P ([|min|] - 1)%Z (cont1 a1) (cont2 a2)).
 assert (P' [|max|] (foldi_down_cont (fun (i : int) (cont : A -> A) (a0 : A) => cont (f1 i a0)) max
                       min (fun a0 : A => a0))
                    (foldi_down_cont (fun (i : int) (cont : A -> A) (a0 : A) => cont (f2 i a0)) max
                       min (fun a0 : A => a0))).
 apply foldi_down_cont_ZInd2;intros;red.
  rewrite Zlt_is_lt_bool in H2;rewrite H2;auto.
  case_eq (Zlt_bool [|i|] [|min|]);intros.
  rewrite <- Zlt_is_lt_bool in H5;rewrite leb_spec in H2;elimtype False;omega.
  clear H5;revert H4;unfold P'.
  case_eq (Zlt_bool ([|i|] - 1) [|min|]);intros;auto.
  rewrite <- Zlt_is_lt_bool in H4; assert ([|i|] = [|min|]) by (rewrite leb_spec in H2;omega).
  destruct H5;subst;rewrite <- H7;apply H1;trivial.
 revert H2;unfold P'.
 case_eq (Zlt_bool [|max|] [|min|]);auto.
 rewrite <- Zlt_is_lt_bool, <- ltb_spec;intros;rewrite foldi_down_cont_lt;auto.
 destruct H3. rewrite H4;auto.
Qed.

Lemma foldi_down_eq_compat : forall A (f1 f2:int -> A -> A) max min a,
  (forall i a, min <= i = true -> i <= max = true -> f1 i a = f2 i a) ->
  foldi_down f1 max min a = foldi_down f2 max min a.
Proof.
 intros; set (P' (z:Z) (a1 a2:A) := a1 = a2).
 assert (P' ([|min|] - 1)%Z (foldi_down f1 max min a) (foldi_down f2 max min a)).
 apply foldi_down_ZInd2;unfold P';intros;subst;auto.
 apply H0.
Qed.

Lemma forallb_spec : forall f from to, 
  forallb f from to = true <->
  forall i, from <= i = true -> i <= to = true -> f i = true.
Proof.
 unfold forallb;intros f from to.
 setoid_rewrite leb_spec.
 apply foldi_cont_ZInd.
 intros;split;[intros;elimtype False;omega | trivial].
 intros i cont Hfr Hto Hcont.
 case_eq (f i);intros Heq.
 rewrite Hcont;clear Hcont;split;auto with zarith;intros.
 assert (H2 : ([|i0|] = [|i|] \/ [|i|] + 1 <= [|i0|])%Z) by omega; destruct H2;auto with zarith.
 apply to_Z_inj in H2;rewrite H2;trivial.
 split;[discriminate | intros].
 rewrite leb_spec in Hto;rewrite <- Heq;auto with zarith.
Qed.

Lemma forallb_eq_compat : forall f1 f2 from to,
  (forall i, from <= i = true -> i <= to = true -> f1 i = f2 i) ->
  forallb f1 from to = forallb f2 from to.
Proof.
 unfold forallb;intros.
 set (P' (z:Z) (cont1 cont2:unit -> bool) := cont1 tt = cont2 tt).
 refine (foldi_cont_ZInd2 _ _ P' _ _ from to _ _ _ _);unfold P';intros;trivial.
 rewrite H2, H;trivial.
Qed.

Lemma existsb_spec : forall f from to,
  existsb f from to = true <->
  exists i, ((from <= i) && (i <= to) && (f i)) = true .
Proof.
 unfold existsb;intros.
 repeat setoid_rewrite andb_true_iff;setoid_rewrite leb_spec.
 apply foldi_cont_ZInd.
 intros;split;[discriminate | intros [i [W1 W2]];elimtype False;omega].
 intros i cont Hfr Hto Hcont.
 case_eq (f i);intros Heq.
  split;trivial.
  exists i;rewrite leb_spec in Hto;auto with zarith.
 rewrite Hcont;clear Hcont;split;intros [i0 [W1 W2]];
  exists i0;split;auto with zarith.
 assert (~ [|i|] = [|i0|]);[ | auto with zarith].
 intros W;apply to_Z_inj in W;rewrite W in Heq;rewrite Heq in W2;discriminate.
Qed.

Lemma existsb_eq_compat : forall f1 f2 from to,
  (forall i, from <= i = true -> i <= to = true -> f1 i = f2 i) ->
  existsb f1 from to = existsb f2 from to.
Proof.
 unfold existsb;intros.
 set (P' (z:Z) (cont1 cont2:unit -> bool) := cont1 tt = cont2 tt).
 refine (foldi_cont_ZInd2 _ _ P' _ _ from to _ _ _ _);unfold P';intros;trivial.
 rewrite H2, H;trivial.
Qed.

Lemma bit_max_int : forall i, (i < digits)%int31 = true -> bit max_int i = true.
Proof.
 intros;apply (forallb_spec (bit max_int) 0 (digits - 1)).
 vm_compute;trivial.
 apply leb_0.
 rewrite ltb_spec in H.
 destruct (to_Z_bounded i);rewrite leb_spec.
 change [|digits - 1 |] with ([|digits|] - 1)%Z;omega.
Qed.

Lemma land_max_int_l : forall i, max_int land i = i.
Proof.
  intros;apply bit_eq;intros.
  rewrite land_spec.
  destruct (reflect_leb digits i0).
  rewrite <- leb_spec in z.
  rewrite !bit_M;trivial.
  rewrite bit_max_int;trivial.
  rewrite ltb_spec;omega.
Qed.

Lemma land_max_int_r : forall i, i land max_int = i.
Proof.
 intros;rewrite land_comm;apply land_max_int_l.
Qed.

