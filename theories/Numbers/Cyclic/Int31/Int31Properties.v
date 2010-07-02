Require Import Zgcd_alt.
Require Import Bvector.
Require Export Int31Axioms.


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

(** Bijection : int <-> Bvector size *)
Lemma of_vect_inj : forall x y, of_vect x = of_vect y -> x = y.
Proof.
 intros.
 rewrite <- (to_of_vect x), <- (to_of_vect y), H;trivial.
Qed.

Lemma of_to_vect : forall x, of_vect (to_vect x) = x.
Proof.
 intros;apply to_vect_inj.
 rewrite to_of_vect;trivial.
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


Lemma to_Z_to_vect : forall x, to_Z x = Z_of_N (Bv2N size (to_vect x)).
Proof.
 unfold to_Z, to_vect;generalize size.
 induction n;simpl;intros;trivial.
 destruct (is_even x);simpl.
 rewrite Z_of_N_double, IHn;trivial.
 rewrite Z_of_N_double_plus_one, IHn;trivial.
Qed.

Lemma of_vect_rec_false : forall n, of_vect_rec n (Bvect_false n) = 0%int31.
Proof.
 induction n;simpl;trivial.
 unfold Bvect_false in IHn;rewrite IHn;trivial.
Qed.


Lemma of_Z_of_vect_pos : forall p, of_Z (Zpos p) = of_vect (N2Bv_gen size (Npos p)).
Proof.
 unfold of_Z, of_pos, of_vect;induction size;simpl;intros;trivial.
 destruct p;simpl;try (rewrite IHn;trivial).
 rewrite of_vect_rec_false;trivial.
Qed.

Lemma of_Z_of_vect_N : forall n, of_Z (Z_of_N n) = of_vect (N2Bv_gen size n).
Proof.
 destruct n;trivial.
 apply of_Z_of_vect_pos.
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

Lemma of_to_Z : forall x, of_Z ([|x|]) = x.
Proof.
 intros x; assert ([|x|] = Z_of_N (N_of_Z ([|x|]))).
   destruct (to_Z_bounded x);destruct [|x|];trivial.
   elim H;trivial.
 rewrite H.
 rewrite of_Z_of_vect_N.
 rewrite to_Z_to_vect.
 assert (forall n, N_of_Z (Z_of_N n) = n) by (destruct n;trivial).
 rewrite H0, N2Bv_Bv2N, of_to_vect;trivial.
Qed.

Lemma is_even_lor1 : forall x, is_even ( x lor 1) = false.
Proof.
 intros.
 unfold is_even, is_zero.
 apply not_true_iff_false.
 intros Heq;rewrite eqb_spec in Heq.
 assert (W:= land_spec (x lor 1) 1).
 rewrite Heq, lor_spec in W.
 unfold to_vect in W;simpl in W.
 injection W;clear W.
 compute; do 30 intro;clear.
 destruct (x land 1 == 0)%int31;discriminate.
Qed.

Lemma to_of_pos : forall p, [|of_pos p|] = Zpos p mod wB.
Proof.
 unfold to_Z, of_pos, wB;induction size;intros.
 simpl;rewrite Zmod_1_r;trivial.
 rewrite inj_S;simpl.
 destruct p.
 rewrite is_even_lor1.
 (*** WARNING : *) 
Admitted.

Lemma to_of_Z : forall z, [| of_Z z |] = z mod wB.
Proof.
 destruct z;trivial; simpl of_Z.
 rewrite to_of_pos;trivial.
 unfold opp;rewrite sub_spec.
 rewrite to_of_pos.
 replace [|0|] with 0;trivial.
 ring_simplify (0 - Zpos p mod wB).
 change (Zneg p) with (- (Zpos p)).
 destruct (Z_eq_dec (Zpos p mod wB) 0).
 rewrite e. change (-0) with 0;rewrite Zmod_0_l.
 rewrite Z_mod_zero_opp_full;trivial.
 assert (W:= wB_diff_0); assert (W0:= wB_pos).
 rewrite Z.mod_opp_l_nz;trivial.
 rewrite Z.mod_opp_l_nz;trivial.
 rewrite Zmod_small;trivial.
 apply Z_mod_lt;auto with zarith.
 rewrite Zmod_small;trivial.
 apply Z_mod_lt;auto with zarith.
Qed.

Lemma to_Z_inj : forall x y, [|x|] = [|y|] -> x = y.
Proof.
 intros x y Heq.
 rewrite <- (of_to_Z x), <- (of_to_Z y), Heq;trivial.
Qed.

(** leb *)
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

(** Iterators *)

Lemma foldi_gt : forall A f from to (a:A), 
  (to < from)%int31 = true -> foldi f from to a = a.
Proof.
 intros;apply foldi_cont_gt;trivial.
Qed.

Lemma foldi_eq : forall A f from to (a:A),
  from = to -> foldi f from to a = f from a.
Proof.
 intros;apply foldi_cont_eq;trivial.
Qed.

Lemma foldi_lt : forall A f from to (a:A), 
  (from < to)%int31 = true -> foldi f from to a = foldi f (from + 1) to (f from a).
Proof.
 intros;apply foldi_cont_lt;trivial.
Qed.

Lemma fold_gt : forall A f from to (a:A), 
  (to < from)%int31 = true -> fold f from to a = a.
Proof.
 intros;apply foldi_cont_gt;trivial.
Qed.

Lemma fold_eq : forall A f from to (a:A),
  from = to -> fold f from to a = f a.
Proof.
 intros;apply foldi_cont_eq;trivial.
Qed.

Lemma fold_lt : forall A f from to (a:A), 
  (from < to)%int31 = true -> fold f from to a = fold f (from + 1) to (f a).
Proof.
 intros;apply foldi_cont_lt;trivial.
Qed.

Lemma foldi_down_lt : forall A f from downto (a:A),
  (from < downto)%int31 = true -> foldi_down f from downto a = a.
Proof.
 intros;apply foldi_down_cont_lt;trivial.
Qed.

Lemma foldi_down_eq : forall A f from downto (a:A),
  from = downto -> foldi_down f from downto a = f from a.
Proof.
 intros;apply foldi_down_cont_eq;trivial.
Qed.

Lemma foldi_down_gt : forall A f from downto (a:A),
  (downto < from)%int31 = true-> 
  foldi_down f from downto a = 
  foldi_down f (from-1) downto (f from a).
Proof.
 intros;apply foldi_down_cont_gt;trivial.
Qed.

Lemma fold_down_lt : forall A f from downto (a:A),
  (from < downto)%int31 = true -> fold_down f from downto a = a.
Proof.
 intros;apply foldi_down_cont_lt;trivial.
Qed.

Lemma fold_down_eq : forall A f from downto (a:A),
  from = downto -> fold_down f from downto a = f a.
Proof.
 intros;apply foldi_down_cont_eq;trivial.
Qed.

Lemma fold_down_gt : forall A f from downto (a:A),
  (downto < from)%int31 = true-> 
  fold_down f from downto a = 
  fold_down f (from-1) downto (f a).
Proof.
 intros;apply foldi_down_cont_gt;trivial.
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
 assert ([|i - 1|] = [|i|] - 1).
  rewrite sub_spec, Zmod_small;rewrite to_Z_1;auto with zarith.
 assert (i = i - 1 + 1)%int31.
  apply to_Z_inj.
  rewrite add_spec, H2.
  rewrite Zmod_small;rewrite to_Z_1;auto with zarith.
 rewrite H3;apply Hrec.
 rewrite ltb_spec, H2;change [|max_int|] with (wB - 1);auto with zarith.
 apply X;auto with zarith.
 intros;apply (X [|i|]);trivial.
 destruct (to_Z_bounded i);trivial.
Qed.
 
Lemma int_ind_bounded : forall (P:int-> Type) min max,
  [|min|] <= [|max|] ->
  P max ->
  (forall i, ([|min|] <= [|i|] + 1 <= [|max|]) -> P (i + 1)%int31 -> P i) ->
  P min.
Proof.
 intros P min max Hle.
 intros Hmax Hrec.
 assert (W1:= to_Z_bounded max);assert (W2:= to_Z_bounded min).
 assert (forall z, (0 <= z)%Z -> z <= [|max|] - [|min|]  -> forall i, z = [|i|] -> P (max - i)%int31).
 intros z H1;pattern z;apply natlike_rec2;intros;trivial.
 assert (max - i = max)%int31.
  apply to_Z_inj;rewrite sub_spec, <- H0, Zminus_0_r, Zmod_small;auto using to_Z_bounded.
 rewrite H2;trivial.
 assert (W3:= to_Z_bounded i);apply Hrec.
 rewrite sub_spec.
 rewrite Zmod_small;auto with zarith.
 assert (max - i + 1 = max - (i - 1))%int31.
  apply to_Z_inj;rewrite add_spec, !sub_spec, to_Z_1.
  rewrite (Zmod_small ([|max|] - [|i|]));auto with zarith.
  rewrite (Zmod_small ([|i|] - 1));auto with zarith.
  apply f_equal2;auto with zarith.
 rewrite H3;apply X;auto with zarith.
 rewrite sub_spec, to_Z_1, <- H2, Zmod_small;auto with zarith.
 assert (min = max - (max - min))%int31.
  apply to_Z_inj.
  rewrite !sub_spec, !Zmod_small;auto with zarith.
  rewrite Zmod_small;auto with zarith.
 rewrite H;apply (X [| max - min |]);trivial;rewrite sub_spec, Zmod_small;auto with zarith.
Qed.

  
Lemma forallb_spec : forall f from to, 
  forallb f from to = true ->
  forall i, [|from|] <= [|i|] <= [|to|] -> 
  f i = true.
Proof.
 intros.
 generalize i H H0.
 assert ([|from|] <= [|to|]) by auto with zarith.
 clear i H0 H.
 pattern from;apply int_ind_bounded with to;trivial.
 intros;replace i with to;[ | apply to_Z_inj;auto with zarith].
 unfold forallb in H;rewrite foldi_cont_eq in H;trivial.
 destruct (f to);trivial.
 intros;assert ([|i|] <= [|to|]) by auto with zarith.
 destruct (Zle_lt_or_eq _ _ H4).
 unfold forallb in H2;rewrite foldi_cont_lt in H2;
  fold (forallb f (i+1) to) in H2;[ | rewrite ltb_spec;trivial].
 generalize H2;clear H2;case_eq (f i);intros;[ | discriminate].
 elimtype ([|i|] = [|i0|] \/ [|i+1|] <= [|i0|]);intros.
 apply to_Z_inj in H7;subst;trivial.
 auto with zarith.
 rewrite add_spec;destruct (to_Z_bounded to);destruct (to_Z_bounded i);
   rewrite Zmod_small;rewrite to_Z_1;auto with zarith; omega.
 intros;replace i0 with to;[ | apply to_Z_inj;auto with zarith].
 apply to_Z_inj in H5;subst.
 unfold forallb in H2;rewrite foldi_cont_eq in H2;trivial.
 destruct (f to);trivial.
Qed.

Lemma existsb_spec : forall f from to,
  existsb f from to = true ->
  exists i, ((from <= i) && (i <= to))%int31 = true -> f i = true.
Proof.
 intros.
(* Warning *)
Admitted.

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

(* TODO : remove this axiom *)
Lemma is_even_spec : forall x,
      if is_even x then [|x|] mod 2 = 0 else [|x|] mod 2 = 1.
Proof.
 unfold is_even;intros.
Admitted.


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
      | C1 m1 => (m1 >> 1 + 30)%int31
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
(*** WARNING : TODO *)
Admitted.
(*
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
 case_eq (fst (diveucl_21 ih il j) < j)%int31;intros Heq0.
 rewrite ltb_spec in Heq0.
 assert ([|match j +c fst (diveucl_21 ih il j) with
           | C0 m1 => m1 >> 1
           | C1 m1 => (m1 >> 1 + 30)%int31
           end|] = ([|j|] + ([||WW ih il||])/([|j|]))/2).
  generalize (addc_spec j (fst (diveucl_21 ih il j)));
  case addc;unfold interp_carry;rewrite div2_phi;simpl zn2z_to_Z.
  intros i H;rewrite lsr_spec, H;trivial.
  intros i H;rewrite <- H.
(*** Warning : TODO *)
  admit.
 apply Hrec;rewrite H.
  (*** Warning : TODO *)
  admit.
  admit.
 split;auto.
 apply sqrt_test_true; auto.
 apply zn2z_to_Z_pos.
 rewrite <- not_true_iff_false, ltb_spec in Heq0.
 assert (W:= diveucl_21_spec ih il j).
 destruct (diveucl_21 ih il j).
 unfold Zdiv;simpl zn2z_to_Z;rewrite <- W;simpl in Heq0;auto with zarith.
 split;auto.
 apply sqrt_test_true; auto.
 apply zn2z_to_Z_pos.
 rewrite <- not_true_iff_false, ltb_spec in Heq.
 simpl zn2z_to_Z.
 (*** Warning : TODO *)
 admit.
Qed.
*)
(*
 Lemma iter312_sqrt_correct n rec ih il j:
  2^29 <= [|ih|] ->  0 < [|j|] -> phi2 ih il < ([|j|] + 1) ^ 2 ->
  (forall j1, 0 < [|j1|] -> 2^(Z_of_nat n) + [|j1|] <= [|j|] ->
      phi2 ih il < ([|j1|] + 1) ^ 2 ->
       [|rec ih il j1|] ^ 2 <= phi2 ih il < ([|rec ih il j1|] + 1) ^ 2)  ->
  [|iter312_sqrt n rec ih il j|] ^ 2 <= phi2 ih il
      < ([|iter312_sqrt n rec ih il j|] + 1) ^ 2.
 Proof.
 revert rec ih il j; elim n; unfold iter312_sqrt; fold iter312_sqrt; clear n.
 intros rec ih il j Hi Hj Hij Hrec; apply sqrt312_step_correct; auto with zarith.
 intros; apply Hrec; auto with zarith.
 rewrite Zpower_0_r; auto with zarith.
 intros n Hrec rec ih il j Hi Hj Hij HHrec.
 apply sqrt312_step_correct; auto.
 intros j1 Hj1  Hjp1; apply Hrec; auto with zarith.
 intros j2 Hj2 H2j2 Hjp2; apply Hrec; auto with zarith.
 intros j3 Hj3 Hpj3.
 apply HHrec; auto.
 rewrite inj_S, Zpower_Zsucc.
 apply Zle_trans with (2 ^Z_of_nat n + [|j2|])%Z; auto with zarith.
 apply Zle_0_nat.
 Qed.
*)
Lemma sqrt2_spec : forall x y,
       wB/ 4 <= [|x|] ->
       let (s,r) := sqrt2 x y in
          [||WW x y||] = [|s|] ^ 2 + [+|r|] /\
          [+|r|] <= 2 * [|s|].
(* WARNING TODO *)
Admitted.
(*
 Proof.
 intros ih il Hih; unfold sqrt312.
 change [||WW ih il||] with (phi2 ih il).
 assert (Hbin: forall s, s * s + 2* s + 1 = (s + 1) ^ 2) by
  (intros s; ring).
 assert (Hb: 0 <= base) by (red; intros HH; discriminate).
 assert (Hi2: phi2 ih il < (phi Tn + 1) ^ 2).
   change ((phi Tn + 1) ^ 2) with (2^62).
  apply Zle_lt_trans with ((2^31 -1) * base + (2^31 - 1)); auto with zarith.
  2: simpl; unfold Zpower_pos; simpl; auto with zarith.
  case (phi_bounded ih); case (phi_bounded il); intros H1 H2 H3 H4.
  unfold base, Zpower, Zpower_pos in H2,H4; simpl in H2,H4.
  unfold phi2,Zpower, Zpower_pos; simpl iter_pos; auto with zarith.
 case (iter312_sqrt_correct 31 (fun _ _ j => j) ih il Tn); auto with zarith.
 change [|Tn|] with 2147483647; auto with zarith.
 intros j1 _ HH; contradict HH.
 apply Zlt_not_le.
 change [|Tn|] with 2147483647; auto with zarith.
 change (2 ^ Z_of_nat 31) with 2147483648; auto with zarith.
 case (phi_bounded j1); auto with zarith.
 set (s := iter312_sqrt 31 (fun _ _ j : int31 => j) ih il Tn).
 intros Hs1 Hs2.
 generalize (spec_mul_c s s); case mul31c.
 simpl zn2z_to_Z; intros HH.
 assert ([|s|] = 0).
 case (Zmult_integral _ _ (sym_equal HH)); auto.
 contradict Hs2; apply Zle_not_lt; rewrite H.
 change ((0 + 1) ^ 2) with 1.
 apply Zle_trans with (2 ^ Z_of_nat size / 4 * base).
 simpl; auto with zarith.
 apply Zle_trans with ([|ih|] * base); auto with zarith.
 unfold phi2; case (phi_bounded il); auto with zarith.
 intros ih1 il1.
 change [||WW ih1 il1||] with (phi2 ih1 il1).
 intros Hihl1.
 generalize (spec_sub_c il il1).
 case sub31c; intros il2 Hil2.
 simpl interp_carry in Hil2.
 rewrite spec_compare; case Zcompare_spec.
 unfold interp_carry.
 intros H1; split.
 rewrite Zpower_2, <- Hihl1.
 unfold phi2; ring[Hil2 H1].
 replace [|il2|] with (phi2 ih il - phi2 ih1 il1).
 rewrite Hihl1.
 rewrite <-Hbin in Hs2; auto with zarith.
 unfold phi2; rewrite H1, Hil2; ring.
 unfold interp_carry.
 intros H1; contradict Hs1.
 apply Zlt_not_le; rewrite Zpower_2, <-Hihl1.
 unfold phi2.
 case (phi_bounded il); intros _ H2.
 apply Zlt_le_trans with (([|ih|] + 1) * base + 0).
 rewrite Zmult_plus_distr_l, Zplus_0_r; auto with zarith.
 case (phi_bounded il1); intros H3 _.
 apply Zplus_le_compat; auto with zarith.
 unfold interp_carry; change (1 * 2 ^ Z_of_nat size) with base.
 rewrite Zpower_2, <- Hihl1, Hil2.
 intros H1.
 case (Zle_lt_or_eq ([|ih1|] + 1) ([|ih|])); auto with zarith.
 intros H2; contradict Hs2; apply Zle_not_lt.
 replace (([|s|] + 1) ^ 2) with (phi2 ih1 il1 + 2 * [|s|] + 1).
 unfold phi2.
 case (phi_bounded il); intros Hpil _.
 assert (Hl1l: [|il1|] <= [|il|]).
  case (phi_bounded il2); rewrite Hil2; auto with zarith.
 assert ([|ih1|] * base + 2 * [|s|] + 1 <= [|ih|] * base); auto with zarith.
 case (phi_bounded s);  change (2 ^ Z_of_nat size) with base; intros _ Hps.
 case (phi_bounded ih1); intros Hpih1 _; auto with zarith.
 apply Zle_trans with (([|ih1|] + 2) * base); auto with zarith.
 rewrite Zmult_plus_distr_l.
 assert (2 * [|s|] + 1 <= 2 * base); auto with zarith.
 rewrite Hihl1, Hbin; auto.
 intros H2; split.
 unfold phi2; rewrite <- H2; ring.
 replace (base + ([|il|] - [|il1|])) with (phi2 ih il - ([|s|] * [|s|])).
 rewrite <-Hbin in Hs2; auto with zarith.
 rewrite <- Hihl1; unfold phi2; rewrite <- H2; ring.
 unfold interp_carry in Hil2 |- *.
 unfold interp_carry; change (1 * 2 ^ Z_of_nat size) with base.
 assert (Hsih: [|ih - 1|] = [|ih|] - 1).
  rewrite spec_sub, Zmod_small; auto; change [|1|] with 1.
  case (phi_bounded ih); intros H1 H2.
  generalize Hih; change (2 ^ Z_of_nat size / 4) with 536870912.
  split; auto with zarith.
 rewrite spec_compare; case Zcompare_spec.
 rewrite Hsih.
 intros H1; split.
 rewrite Zpower_2, <- Hihl1.
 unfold phi2; rewrite <-H1.
 apply trans_equal with ([|ih|] * base + [|il1|] + ([|il|] - [|il1|])).
 ring.
 rewrite <-Hil2.
 change (2 ^ Z_of_nat size) with base; ring.
 replace [|il2|] with (phi2 ih il - phi2 ih1 il1).
 rewrite Hihl1.
 rewrite <-Hbin in Hs2; auto with zarith.
 unfold phi2.
 rewrite <-H1.
 ring_simplify.
 apply trans_equal with (base + ([|il|] - [|il1|])).
 ring.
 rewrite <-Hil2.
 change (2 ^ Z_of_nat size) with base; ring.
 rewrite Hsih; intros H1.
 assert (He: [|ih|] = [|ih1|]).
   apply Zle_antisym; auto with zarith.
   case (Zle_or_lt [|ih1|] [|ih|]); auto; intros H2.
   contradict Hs1; apply Zlt_not_le; rewrite Zpower_2, <-Hihl1.
  unfold phi2.
  case (phi_bounded il); change (2 ^ Z_of_nat size) with base;
    intros _ Hpil1.
  apply Zlt_le_trans with (([|ih|] + 1) * base).
  rewrite Zmult_plus_distr_l, Zmult_1_l; auto with zarith.
  case (phi_bounded il1); intros Hpil2 _.
  apply Zle_trans with (([|ih1|]) * base); auto with zarith.
 rewrite Zpower_2, <-Hihl1; unfold phi2; rewrite <-He.
 contradict Hs1; apply Zlt_not_le; rewrite Zpower_2, <-Hihl1.
 unfold phi2; rewrite He.
 assert (phi il - phi il1 < 0); auto with zarith.
 rewrite <-Hil2.
 case (phi_bounded il2); auto with zarith.
 intros H1.
 rewrite Zpower_2, <-Hihl1.
 case (Zle_lt_or_eq ([|ih1|] + 2) [|ih|]); auto with zarith.
 intros H2; contradict Hs2; apply Zle_not_lt.
 replace (([|s|] + 1) ^ 2) with (phi2 ih1 il1 + 2 * [|s|] + 1).
 unfold phi2.
 assert ([|ih1|] * base + 2 * phi s + 1 <= [|ih|] * base + ([|il|] - [|il1|]));
  auto with zarith.
 rewrite <-Hil2.
 change (-1 * 2 ^ Z_of_nat size) with (-base).
 case (phi_bounded il2); intros Hpil2 _.
 apply Zle_trans with ([|ih|] * base + - base); auto with zarith.
 case (phi_bounded s);  change (2 ^ Z_of_nat size) with base; intros _ Hps.
 assert (2 * [|s|] + 1 <= 2 * base); auto with zarith.
 apply Zle_trans with ([|ih1|] * base + 2 * base); auto with zarith.
 assert (Hi: ([|ih1|] + 3) * base <= [|ih|] * base); auto with zarith.
 rewrite Zmult_plus_distr_l in Hi; auto with zarith.
 rewrite Hihl1, Hbin; auto.
 intros H2; unfold phi2; rewrite <-H2.
 split.
 replace [|il|] with (([|il|] - [|il1|]) + [|il1|]); try ring.
 rewrite <-Hil2.
 change (-1 * 2 ^ Z_of_nat size) with (-base); ring.
 replace (base + [|il2|]) with (phi2 ih il - phi2 ih1 il1).
 rewrite Hihl1.
 rewrite <-Hbin in Hs2; auto with zarith.
 unfold phi2; rewrite <-H2.
 replace [|il|] with (([|il|] - [|il1|]) + [|il1|]); try ring.
 rewrite <-Hil2.
 change (-1 * 2 ^ Z_of_nat size) with (-base); ring.
Qed.
*)

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

Lemma addmuldiv_spec : forall x y p, [|p|] <= [|digits|] ->
   [| addmuldiv p x y |] =
   ([|x|] * (2 ^ [|p|]) + [|y|] / (2 ^ ([|digits|] - [|p|]))) mod wB.
Proof.
(*** WARNING : TODO *)
Admitted.

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




