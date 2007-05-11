
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Set Implicit Arguments.

Require Import ZArith.
Require Import ZDivModAux.
Require Import ZPowerAux.
Require Import Basic_type.
Require Import GenBase.

Open Local Scope Z_scope.

Section GENDIVN1.

 Variable w             : Set.
 Variable w_digits      : positive.
 Variable w_0           : w.
 Variable w_WW          : w -> w -> zn2z w.
 Variable w_head0       : w -> N.
 Variable w_add_mul_div : positive -> w -> w -> w.
 Variable w_div21       : w -> w -> w -> w * w.
 
 (* ** For proofs ** *)
 Variable w_to_Z        : w -> Z.
 
 Notation wB := (base w_digits). 

 Notation "[| x |]" := (w_to_Z x)  (at level 0, x at level 99).
 Notation "[! n | x !]" := (gen_to_Z w_digits w_to_Z n x) 
                                      (at level 0, x at level 99).
 Notation "[[ x ]]" := (zn2z_to_Z wB w_to_Z x)  (at level 0, x at level 99).
 
 Variable spec_to_Z   : forall x, 0 <= [| x |] < wB.
 Variable spec_0   : [|w_0|] = 0.
 Variable spec_WW  : forall h l, [[w_WW h l]] = [|h|] * wB + [|l|].
 Variable spec_head0  : forall x,  0 < [|x|] ->
	 wB/ 2 <= 2 ^ (Z_of_N (w_head0 x)) * [|x|] < wB.
 Variable spec_add_mul_div : forall x y p,
        Zpos p < Zpos w_digits ->
       [| w_add_mul_div p x y |] =
         ([|x|] * (Zpower 2 (Zpos p)) +
          [|y|] / (Zpower 2 ((Zpos w_digits) - (Zpos p)))) mod wB.
 Variable spec_div21 : forall a1 a2 b,
     wB/2 <= [|b|] ->
     [|a1|] < [|b|] ->
     let (q,r) := w_div21 a1 a2 b in
     [|a1|] *wB+ [|a2|] = [|q|] * [|b|] + [|r|] /\
     0 <= [|r|] < [|b|].
 
 Section DIVAUX.
  Variable b2p : w.
  Variable b2p_le : wB/2 <= [|b2p|].

  Definition gen_divn1_0_aux n (divn1: w -> word w n -> word w n * w) r h :=
   let (hh,hl) := gen_split w_0 n h in
   let (qh,rh) := divn1 r hh in
   let (ql,rl) := divn1 rh hl in
   (gen_WW w_WW n qh ql, rl).

  Fixpoint gen_divn1_0 (n:nat) : w -> word w n -> word w n * w :=
   match n return w -> word w n -> word w n * w with
   | O => fun r x => w_div21 r x b2p 
   | S n => gen_divn1_0_aux n (gen_divn1_0 n) 
   end.
 
  Lemma spec_split : forall (n : nat) (x : zn2z (word w n)),
       let (h, l) := gen_split w_0 n x in
       [!S n | x!] = [!n | h!] * gen_wB w_digits n + [!n | l!].
  Proof (spec_gen_split w_0 w_digits w_to_Z spec_0).

  Lemma spec_gen_divn1_0 : forall n r a,
    [|r|] < [|b2p|] ->
    let (q,r') := gen_divn1_0 n r a in
    [|r|] * gen_wB w_digits n + [!n|a!] = [!n|q!] * [|b2p|] + [|r'|] /\
    0 <= [|r'|] < [|b2p|].
  Proof.
   induction n;intros.
   exact (spec_div21 a b2p_le H).
   unfold gen_divn1_0, gen_divn1_0_aux;fold gen_divn1_0.
   assert (H1 := spec_split n a);destruct (gen_split w_0 n a) as (hh,hl).
   rewrite H1.
   assert (H2 := IHn r hh H);destruct (gen_divn1_0 n r hh) as (qh,rh).
   destruct H2.
   assert ([|rh|] < [|b2p|]). omega.
   assert (H4 := IHn rh hl H3);destruct (gen_divn1_0 n rh hl) as (ql,rl).
   destruct H4;split;trivial.
   rewrite spec_gen_WW;trivial.
   rewrite <- gen_wB_wwB.
   rewrite Zmult_assoc;rewrite Zplus_assoc;rewrite <- Zmult_plus_distr_l.
   rewrite H0;rewrite Zmult_plus_distr_l;rewrite <- Zplus_assoc.
   rewrite H4;ring.
  Qed.

  Definition gen_modn1_0_aux n (modn1:w -> word w n -> w) r h :=
   let (hh,hl) := gen_split w_0 n h in modn1 (modn1 r hh) hl.

  Fixpoint gen_modn1_0 (n:nat) : w -> word w n -> w :=
   match n return w -> word w n -> w with
   | O => fun r x => snd (w_div21 r x b2p)
   | S n => gen_modn1_0_aux n (gen_modn1_0 n)
   end.

  Lemma spec_gen_modn1_0 : forall n r x,
     gen_modn1_0 n r x = snd (gen_divn1_0 n r x).
  Proof.
   induction n;simpl;intros;trivial.
   unfold gen_modn1_0_aux, gen_divn1_0_aux.
   destruct (gen_split w_0 n x) as (hh,hl).
   rewrite (IHn r hh). 
   destruct (gen_divn1_0 n r hh) as (qh,rh);simpl.
   rewrite IHn. destruct (gen_divn1_0 n rh hl);trivial.
  Qed.
 
  Variable p : positive.
  Variable p_bounded : Zpos p < Zpos w_digits.

  Lemma spec_add_mul_divp : forall x y,
    [| w_add_mul_div p x y |] =
       ([|x|] * (Zpower 2 (Zpos p)) +
          [|y|] / (Zpower 2 ((Zpos w_digits) - (Zpos p)))) mod wB.
  Proof.
   intros;apply spec_add_mul_div;auto.
  Qed.

  Definition gen_divn1_p_aux n 
   (divn1 : w -> word w n -> word w n -> word w n * w) r h l := 
   let (hh,hl) := gen_split w_0 n h in
   let (lh,ll) := gen_split w_0 n l in	
   let (qh,rh) := divn1 r hh hl in
   let (ql,rl) := divn1 rh hl lh in
   (gen_WW w_WW n qh ql, rl).

  Fixpoint gen_divn1_p (n:nat) : w -> word w n -> word w n -> word w n * w :=
   match n return w -> word w n -> word w n ->  word w n * w with
   | O => fun r h l => w_div21 r (w_add_mul_div p h l) b2p 
   | S n => gen_divn1_p_aux n (gen_divn1_p n)   
   end.

  Lemma p_lt_gen_digits : forall n, Zpos p < Zpos (gen_digits w_digits n).
  Proof.
   induction n;simpl. destruct p_bounded;trivial.
   assert (0 < Zpos p). unfold Zlt;reflexivity.
   rewrite Zpos_xO;auto with zarith.
  Qed.

  Lemma spec_gen_divn1_p : forall n r h l,
    [|r|] < [|b2p|] ->
    let (q,r') := gen_divn1_p n r h l in
    [|r|] * gen_wB w_digits n + 
      ([!n|h!]*2^(Zpos p) + 
        [!n|l!] / (2^(Zpos(gen_digits w_digits n) - Zpos p)))
        mod gen_wB w_digits n = [!n|q!] * [|b2p|] + [|r'|] /\
    0 <= [|r'|] < [|b2p|].
  Proof.
   induction n;intros.
   unfold gen_divn1_p, gen_divn1_p_aux, gen_to_Z, gen_wB, gen_digits.
   rewrite <- spec_add_mul_divp.
   exact (spec_div21 (w_add_mul_div p h l) b2p_le H).
   unfold gen_divn1_p,gen_divn1_p_aux;fold gen_divn1_p.
   assert (H1 := spec_split n h);destruct (gen_split w_0 n h) as (hh,hl).
   rewrite H1. rewrite <- gen_wB_wwB.
   assert (H2 := spec_split n l);destruct (gen_split w_0 n l) as (lh,ll).
   rewrite H2.
   replace ([|r|] * (gen_wB w_digits n * gen_wB w_digits n) +
    (([!n|hh!] * gen_wB w_digits n + [!n|hl!]) * 2 ^ Zpos p +
    ([!n|lh!] * gen_wB w_digits n + [!n|ll!]) /
     2^(Zpos (gen_digits w_digits (S n)) - Zpos p)) mod
      (gen_wB w_digits n * gen_wB w_digits n)) with
    (([|r|] * gen_wB w_digits n + ([!n|hh!] * 2^Zpos p + 
      [!n|hl!] / 2^(Zpos (gen_digits w_digits n) - Zpos p)) mod
                      gen_wB w_digits n) * gen_wB w_digits n +
     ([!n|hl!] * 2^Zpos p + 
      [!n|lh!] / 2^(Zpos (gen_digits w_digits n) - Zpos p)) mod 
              gen_wB w_digits n).
   generalize (IHn r hh hl H);destruct (gen_divn1_p n r hh hl) as (qh,rh);
   intros (H3,H4);rewrite H3.
   assert ([|rh|] < [|b2p|]). omega. 
   replace (([!n|qh!] * [|b2p|] + [|rh|]) * gen_wB w_digits n +
     ([!n|hl!] * 2 ^ Zpos p +
      [!n|lh!] / 2 ^ (Zpos (gen_digits w_digits n) - Zpos p)) mod
      gen_wB w_digits n)  with  
    ([!n|qh!] * [|b2p|] *gen_wB w_digits n + ([|rh|]*gen_wB w_digits n +
      ([!n|hl!] * 2 ^ Zpos p +
       [!n|lh!] / 2 ^ (Zpos (gen_digits w_digits n) - Zpos p)) mod
      gen_wB w_digits n)). 2:ring.
   generalize (IHn rh hl lh H0);destruct (gen_divn1_p n rh hl lh) as (ql,rl);
   intros (H5,H6);rewrite H5.
   split;[rewrite spec_gen_WW;trivial;ring|trivial]. 
   assert (Uhh := spec_gen_to_Z w_digits w_to_Z spec_to_Z n hh);
    unfold gen_wB,base in Uhh.
   assert (Uhl := spec_gen_to_Z w_digits w_to_Z spec_to_Z n hl);
    unfold gen_wB,base in Uhl.
   assert (Ulh := spec_gen_to_Z w_digits w_to_Z spec_to_Z n lh);
    unfold gen_wB,base in Ulh.
   assert (Ull := spec_gen_to_Z w_digits w_to_Z spec_to_Z n ll);
    unfold gen_wB,base in Ull.
   unfold gen_wB,base.
   assert (UU:=p_lt_gen_digits n).
   rewrite Zdiv_shift_r;auto with zarith. 
   2:change (Zpos (gen_digits w_digits (S n))) 
     with (2*Zpos (gen_digits w_digits n));auto with zarith.
   replace (2 ^ (Zpos (gen_digits w_digits (S n)) - Zpos p)) with
    (2^(Zpos (gen_digits w_digits n) - Zpos p)*2^Zpos (gen_digits w_digits n)).
   rewrite Zdiv_Zmult_compat_r;auto with zarith.
   rewrite Zmult_plus_distr_l with (p:=  2^Zpos p). 
   pattern  ([!n|hl!] * 2^Zpos p) at 2;
   rewrite (shift_unshift_mod (Zpos(gen_digits w_digits n))(Zpos p)([!n|hl!]));
    auto with zarith.
   rewrite Zplus_assoc. 
   replace 
    ([!n|hh!] * 2^Zpos (gen_digits w_digits n)* 2^Zpos p +
      ([!n|hl!] / 2^(Zpos (gen_digits w_digits n)-Zpos p)*
       2^Zpos(gen_digits w_digits n)))
   with 
    (([!n|hh!] *2^Zpos p + gen_to_Z w_digits w_to_Z n hl / 
       2^(Zpos (gen_digits w_digits n)-Zpos p))
      * 2^Zpos(gen_digits w_digits n));try (ring;fail).
   rewrite <- Zplus_assoc.
   rewrite <- (Zmod_shift_r (Zpos p));auto with zarith.
   replace 
     (2 ^ Zpos (gen_digits w_digits n) * 2 ^ Zpos (gen_digits w_digits n)) with
     (2 ^ (Zpos (gen_digits w_digits n) + Zpos (gen_digits w_digits n))).
   rewrite (Zmod_shift_r (Zpos (gen_digits w_digits n)));auto with zarith.
   replace (2 ^ (Zpos (gen_digits w_digits n) + Zpos (gen_digits w_digits n)))
   with (2^Zpos(gen_digits w_digits n) *2^Zpos(gen_digits w_digits n)). 
   rewrite (Zmult_comm (([!n|hh!] * 2 ^ Zpos p +
      [!n|hl!] / 2 ^ (Zpos (gen_digits w_digits n) - Zpos p)))).
   rewrite  Zmod_Zmult_compat_l;auto with zarith.
   ring. 
   rewrite Zpower_exp;auto with zarith.
   assert (0 < Zpos (gen_digits w_digits n)). unfold Zlt;reflexivity.
   auto with zarith.
   apply Z_mod_lt;auto with zarith.
   rewrite Zpower_exp;auto with zarith.
   split;auto with zarith.
   apply Zdiv_lt_upper_bound;auto with zarith.
   rewrite <- Zpower_exp;auto with zarith.
   replace (Zpos p + (Zpos (gen_digits w_digits n) - Zpos p)) with 
     (Zpos(gen_digits w_digits n));auto with zarith.
   assert (0 < Zpos p). unfold Zlt;reflexivity. auto with zarith.
   rewrite <- Zpower_exp;auto with zarith.
   replace (Zpos (gen_digits w_digits (S n)) - Zpos p) with 
       (Zpos (gen_digits w_digits n) - Zpos p + 
         Zpos (gen_digits w_digits n));trivial.
   change (Zpos (gen_digits w_digits (S n))) with 
    (2*Zpos (gen_digits w_digits n)). ring.
  Qed.

  Definition gen_modn1_p_aux n (modn1 : w -> word w n -> word w n -> w) r h l:=
   let (hh,hl) := gen_split w_0 n h in
   let (lh,ll) := gen_split w_0 n l in	
   modn1 (modn1 r hh hl) hl lh.

  Fixpoint gen_modn1_p (n:nat) : w -> word w n -> word w n -> w :=
   match n return w -> word w n -> word w n -> w with
   | O => fun r h l => snd (w_div21 r (w_add_mul_div p h l) b2p) 
   | S n => gen_modn1_p_aux n (gen_modn1_p n)
   end.

  Lemma spec_gen_modn1_p : forall n r h l ,
    gen_modn1_p n r h l = snd (gen_divn1_p n r h l).
  Proof.
   induction n;simpl;intros;trivial.
   unfold gen_modn1_p_aux, gen_divn1_p_aux.
   destruct(gen_split w_0 n h)as(hh,hl);destruct(gen_split w_0 n l) as (lh,ll).
   rewrite (IHn r hh hl);destruct (gen_divn1_p n r hh hl) as (qh,rh).
   rewrite IHn;simpl;destruct (gen_divn1_p n rh hl lh);trivial.
  Qed.

 End DIVAUX.

 Fixpoint hight (n:nat) : word w n -> w :=
  match n return word w n -> w with
  | O => fun a => a 
  | S n => 
    fun (a:zn2z (word w n)) =>
     match a with
     | W0 => w_0
     | WW h l => hight n h
     end
  end.

 Lemma spec_gen_digits:forall n, Zpos w_digits <= Zpos (gen_digits w_digits n).
 Proof.
  induction n;simpl;auto with zarith.
  change (Zpos (xO (gen_digits w_digits n))) with 
    (2*Zpos (gen_digits w_digits n)).
  assert (0 < Zpos w_digits);auto with zarith.
  exact (refl_equal Lt).
 Qed.

 Lemma spec_hight : forall n (x:word w n), 
   [|hight n x|] = [!n|x!] / 2^(Zpos (gen_digits w_digits n) - Zpos w_digits).
 Proof.
  induction n;intros.
  unfold hight,gen_digits,gen_to_Z.
  replace (Zpos w_digits - Zpos w_digits) with 0;try ring.
  simpl. rewrite <- (Zdiv_unique [|x|] 1 [|x|] 0);auto with zarith.
  assert (U2 := spec_gen_digits n). 
  assert (U3 : 0 < Zpos w_digits). exact (refl_equal Lt).
  destruct x;unfold hight;fold hight.
  unfold gen_to_Z,zn2z_to_Z;rewrite spec_0.
  rewrite Zdiv_0;trivial.
  apply Zpower_lt_0;auto with zarith.
  change (Zpos (gen_digits w_digits (S n))) with 
    (2*Zpos (gen_digits w_digits n)).
  auto with zarith.
  assert (U0 := spec_gen_to_Z w_digits w_to_Z spec_to_Z n w0);
   assert (U1 := spec_gen_to_Z w_digits w_to_Z spec_to_Z n w1).
  unfold gen_to_Z,zn2z_to_Z;fold (gen_to_Z w_digits w_to_Z).
  unfold gen_wB,base;rewrite Zdiv_shift_r;auto with zarith.
  replace (2 ^ (Zpos (gen_digits w_digits (S n)) - Zpos w_digits)) with
   (2^(Zpos (gen_digits w_digits n) - Zpos w_digits) * 
        2^Zpos (gen_digits w_digits n)).
  rewrite Zdiv_Zmult_compat_r;auto with zarith.
  rewrite <- Zpower_exp;auto with zarith.
  replace (Zpos (gen_digits w_digits n) - Zpos w_digits + 
    Zpos (gen_digits w_digits n)) with
   (Zpos (gen_digits w_digits (S n)) - Zpos w_digits);trivial.
  change (Zpos (gen_digits w_digits (S n))) with 
     (2*Zpos (gen_digits w_digits n));ring.
  change (Zpos (gen_digits w_digits (S n))) with 
  (2*Zpos (gen_digits w_digits n)); auto with zarith.
 Qed.
 
 Definition gen_divn1 (n:nat) (a:word w n) (b:w) := 
  match w_head0 b with
  | N0 => gen_divn1_0 b n w_0 a 
  | Npos p =>
    let b2p := w_add_mul_div p b w_0 in
    let ha := hight n a in
    let k := Pminus w_digits p in
    let lsr_n := w_add_mul_div k w_0 in 
    let r0 := w_add_mul_div p w_0 ha in
    let (q,r) := gen_divn1_p b2p p n r0 a (gen_0 w_0 n) in
    (q, lsr_n r)
  end.

 Lemma spec_gen_divn1 : forall n a b,
    0 < [|b|] ->
    let (q,r) := gen_divn1 n a b in
    [!n|a!] = [!n|q!] * [|b|] + [|r|] /\
    0 <= [|r|] < [|b|].
  Proof.
   intros n a b H. unfold gen_divn1.
   assert (H0 := spec_head0 H).
   destruct (w_head0 b).
   unfold Z_of_N, Zpower in H0.
   rewrite Zmult_1_l in H0;destruct H0.
   rewrite <- spec_0 in H.
   assert (H2 := spec_gen_divn1_0 H0 n a H).
   rewrite spec_0 in H2;rewrite Zmult_0_l in H2;rewrite Zplus_0_l in H2.
   exact H2.
   unfold Z_of_N in H0.
   assert (HHHH : 0 < Zpos p). unfold Zlt;reflexivity.
   assert (Zpos p < Zpos w_digits).
    destruct (Z_lt_le_dec (Zpos p) (Zpos w_digits));trivial.
    assert (2 ^ Zpos p < wB).
     apply Zle_lt_trans with (2 ^ Zpos p * [|b|]);auto with zarith.
     replace (2 ^ Zpos p) with (2^Zpos p * 1);try (ring;fail).
     apply Zmult_le_compat;auto with zarith.
     assert (wB <= 2^Zpos p).
     unfold base;apply Zpower_le_monotone;auto with zarith. omega.
   assert ([|w_add_mul_div p b w_0|] = 2 ^ Zpos p * [|b|]).
    assert (H2 := spec_add_mul_div b w_0 H1).
    rewrite spec_0 in H2;rewrite Zdiv_0 in H2;
    rewrite Zplus_0_r in H2;rewrite Zmult_comm in H2.
    rewrite Zmod_def_small in H2;auto with zarith.
    apply Zpower_lt_0;auto with zarith.
   destruct H0.
   assert (H4 := spec_to_Z (hight n a)).
   assert 
    ([|w_add_mul_div p w_0 (hight n a)|]<[|w_add_mul_div p b w_0|]).
    rewrite H2.
    rewrite spec_add_mul_div;auto with zarith.
    rewrite spec_0;rewrite Zmult_0_l;rewrite Zplus_0_l.
    assert (([|hight n a|]/2^(Zpos w_digits - Zpos p)) < wB).
     apply Zdiv_lt_upper_bound;auto with zarith. 
     apply Zlt_le_trans with wB;auto with zarith.
     pattern wB at 1;replace wB with (wB*1);try ring.
     apply Zmult_le_compat;auto with zarith.
     assert (H5 := Zpower_lt_0 2 (Zpos w_digits - Zpos p));
       auto with zarith.
    rewrite Zmod_def_small;auto with zarith.
    apply Zdiv_lt_upper_bound;auto with zarith.
    apply Zlt_le_trans with wB;auto with zarith.
    apply Zle_trans with (2 ^ Zpos p * [|b|] * 2).
    rewrite <- wB_div_2;auto with zarith.
    apply Zmult_le_compat;auto with zarith.
    pattern 2 at 1;rewrite <- Zpower_exp_1.
    apply Zpower_le_monotone;split;auto with zarith.
   rewrite <- H2 in H0. 
   assert (H6:= spec_gen_divn1_p H0 H1 n a (gen_0 w_0 n) H5).
   destruct (gen_divn1_p (w_add_mul_div p b w_0) p n
             (w_add_mul_div p w_0 (hight n a)) a
             (gen_0 w_0 n)) as (q,r).
   assert (U:= spec_gen_digits n).
   rewrite spec_gen_0 in H6;trivial;rewrite Zdiv_0 in H6.
   rewrite Zplus_0_r in H6.
   rewrite spec_add_mul_div in H6;auto with zarith.
   rewrite spec_0 in H6;rewrite Zmult_0_l in H6;rewrite Zplus_0_l in H6.
   assert (([|hight n a|] / 2 ^ (Zpos w_digits - Zpos p)) mod wB
     = [!n|a!] / 2^(Zpos (gen_digits w_digits n) - Zpos p)).
   rewrite Zmod_def_small;auto with zarith.
   rewrite spec_hight. rewrite Zdiv_Zdiv;auto with zarith.
   rewrite <- Zpower_exp;auto with zarith.
   replace (Zpos (gen_digits w_digits n) - Zpos w_digits + 
                       (Zpos w_digits - Zpos p))
    with (Zpos (gen_digits w_digits n) - Zpos p);trivial;ring.
   assert (H7 := Zpower_lt_0 2  (Zpos w_digits - Zpos p));auto with zarith.
   split;auto with zarith.
   apply Zle_lt_trans with ([|hight n a|]);auto with zarith.
   apply Zdiv_le_upper_bound;auto with zarith.
   pattern ([|hight n a|]) at 1;rewrite <- Zmult_1_r.
   apply Zmult_le_compat;auto with zarith.
   rewrite H7 in H6;unfold gen_wB,base in H6.
   rewrite <- shift_unshift_mod in H6;auto with zarith.
   rewrite H2 in H6.
   assert ([|w_add_mul_div (w_digits - p) w_0 r|] = [|r|]/2^Zpos p).
   rewrite spec_add_mul_div.
   rewrite spec_0;rewrite Zmult_0_l;rewrite Zplus_0_l.
   replace (Zpos w_digits - Zpos (w_digits - p)) with (Zpos p).
   rewrite Zmod_def_small;auto with zarith.
   assert (H8 := spec_to_Z r).
   split;auto with zarith.
   apply Zle_lt_trans with ([|r|]);auto with zarith.
   apply Zdiv_le_upper_bound;auto with zarith.
   pattern ([|r|]) at 1;rewrite <- Zmult_1_r.
   apply Zmult_le_compat;auto with zarith.
   assert (H9 := Zpower_lt_0 2  (Zpos p));auto with zarith.
   rewrite Zpos_minus;auto with zarith.
   rewrite Zpos_minus;auto with zarith.
   destruct H6.
   split.
   rewrite <- (Z_div_mult [!n|a!] (2^Zpos p));auto with zarith.
   rewrite H8;rewrite H6.
   replace ([!n|q!] * (2 ^ Zpos p * [|b|])) with ([!n|q!] *[|b|] * 2^Zpos p);
     try (ring;fail).
   rewrite Z_div_plus_l;auto with zarith.
   assert (H10 := spec_to_Z (w_add_mul_div (w_digits - p) w_0 r));split;
    auto with zarith.
   rewrite H8.
   apply Zdiv_lt_upper_bound;auto with zarith.
   rewrite Zmult_comm;auto with zarith.
   exact (spec_gen_to_Z w_digits w_to_Z spec_to_Z n a).
   apply Zpower_lt_0;auto with zarith.
 Qed.

 Definition gen_modn1 (n:nat) (a:word w n) (b:w) := 
  match w_head0 b with
  | N0 => gen_modn1_0 b n w_0 a 
  | Npos p =>
    let b2p := w_add_mul_div p b w_0 in
    let ha := hight n a in
    let k := Pminus w_digits p in
    let lsr_n := w_add_mul_div k w_0 in 
    let r0 := w_add_mul_div p w_0 ha in
    let r := gen_modn1_p b2p p n r0 a (gen_0 w_0 n) in
    lsr_n r
  end.

 Lemma spec_gen_modn1_aux : forall n a b,
    gen_modn1 n a b = snd (gen_divn1 n a b).
 Proof.
  intros n a b;unfold gen_divn1,gen_modn1.
  destruct (w_head0 b).
  apply spec_gen_modn1_0.
  rewrite spec_gen_modn1_p.
  destruct (gen_divn1_p (w_add_mul_div p b w_0) p n
            (w_add_mul_div p w_0 (hight n a)) a (gen_0 w_0 n));simpl;trivial.
 Qed.

 Lemma spec_gen_modn1 : forall n a b, 0 < [|b|] ->
  [|gen_modn1 n a b|] = [!n|a!] mod [|b|].
 Proof.
  intros n a b H;assert (H1 := spec_gen_divn1 n a H).
  assert (H2 := spec_gen_modn1_aux n a b).
  rewrite H2;destruct (gen_divn1 n a b) as (q,r).
  simpl;apply Zmod_unique with (gen_to_Z w_digits w_to_Z n q);auto with zarith.
  destruct H1 as (h1,h2);rewrite h1;ring.
 Qed.

End GENDIVN1. 
