
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Set Implicit Arguments.

Require Import ZArith.
Require Import ZAux.
Require Import Basic_type.
Require Import GenBase.

Open Local Scope Z_scope.

Section GENDIVN1.

 Variable w             : Set.
 Variable w_digits      : positive.
 Variable w_zdigits     : w.
 Variable w_0           : w.
 Variable w_WW          : w -> w -> zn2z w.
 Variable w_head0       : w -> w.
 Variable w_add_mul_div : w -> w -> w -> w.
 Variable w_div21       : w -> w -> w -> w * w.
 Variable w_compare     : w -> w -> comparison.
 Variable w_sub         : w -> w -> w.
 

 
 (* ** For proofs ** *)
 Variable w_to_Z        : w -> Z.
 
 Notation wB := (base w_digits). 

 Notation "[| x |]" := (w_to_Z x)  (at level 0, x at level 99).
 Notation "[! n | x !]" := (gen_to_Z w_digits w_to_Z n x) 
                                      (at level 0, x at level 99).
 Notation "[[ x ]]" := (zn2z_to_Z wB w_to_Z x)  (at level 0, x at level 99).
 
 Variable spec_to_Z   : forall x, 0 <= [| x |] < wB.
 Variable spec_w_zdigits: [|w_zdigits|] = Zpos w_digits.
 Variable spec_0   : [|w_0|] = 0.
 Variable spec_WW  : forall h l, [[w_WW h l]] = [|h|] * wB + [|l|].
 Variable spec_head0  : forall x,  0 < [|x|] ->
	 wB/ 2 <= 2 ^ [|w_head0 x|] * [|x|] < wB.
 Variable spec_add_mul_div : forall x y p,
        [|p|] <= Zpos w_digits ->
       [| w_add_mul_div p x y |] =
         ([|x|] * (2 ^ [|p|]) +
          [|y|] / (2 ^ ((Zpos w_digits) - [|p|]))) mod wB.
 Variable spec_div21 : forall a1 a2 b,
     wB/2 <= [|b|] ->
     [|a1|] < [|b|] ->
     let (q,r) := w_div21 a1 a2 b in
     [|a1|] *wB+ [|a2|] = [|q|] * [|b|] + [|r|] /\
     0 <= [|r|] < [|b|].
 Variable spec_compare :
     forall x y,
       match w_compare x y with
       | Eq => [|x|] = [|y|]
       | Lt => [|x|] < [|y|]
       | Gt => [|x|] > [|y|]
       end.
 Variable spec_sub: forall x y, 
   [|w_sub x y|] = ([|x|] - [|y|]) mod wB.

 

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
   simpl (gen_divn1_0 (S n) r a); unfold gen_divn1_0_aux.
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
 
  Variable p : w.
  Variable p_bounded : [|p|] <= Zpos w_digits.

  Lemma spec_add_mul_divp : forall x y,
    [| w_add_mul_div p x y |] =
       ([|x|] * (2 ^ [|p|]) +
          [|y|] / (2 ^ ((Zpos w_digits) - [|p|]))) mod wB.
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

  Lemma p_lt_gen_digits : forall n, [|p|] <= Zpos (gen_digits w_digits n).
  Proof.
(*
   induction n;simpl. destruct p_bounded;trivial.
   case (spec_to_Z p); rewrite Zpos_xO;auto with zarith.
*)
   induction n;simpl. trivial.
   case (spec_to_Z p); rewrite Zpos_xO;auto with zarith.
  Qed.

  Lemma spec_gen_divn1_p : forall n r h l,
    [|r|] < [|b2p|] ->
    let (q,r') := gen_divn1_p n r h l in
    [|r|] * gen_wB w_digits n + 
      ([!n|h!]*2^[|p|] + 
        [!n|l!] / (2^(Zpos(gen_digits w_digits n) - [|p|])))
        mod gen_wB w_digits n = [!n|q!] * [|b2p|] + [|r'|] /\
    0 <= [|r'|] < [|b2p|].
  Proof.
   case (spec_to_Z p); intros HH0 HH1.
   induction n;intros.
   simpl (gen_divn1_p 0 r h l).
   unfold gen_to_Z, gen_wB, gen_digits.
   rewrite <- spec_add_mul_divp.
   exact (spec_div21 (w_add_mul_div p h l) b2p_le H).
   simpl (gen_divn1_p (S n) r h l).
   unfold gen_divn1_p_aux.
   assert (H1 := spec_split n h);destruct (gen_split w_0 n h) as (hh,hl).
   rewrite H1. rewrite <- gen_wB_wwB.
   assert (H2 := spec_split n l);destruct (gen_split w_0 n l) as (lh,ll).
   rewrite H2.
   replace ([|r|] * (gen_wB w_digits n * gen_wB w_digits n) +
    (([!n|hh!] * gen_wB w_digits n + [!n|hl!]) * 2 ^ [|p|] +
    ([!n|lh!] * gen_wB w_digits n + [!n|ll!]) /
     2^(Zpos (gen_digits w_digits (S n)) - [|p|])) mod
      (gen_wB w_digits n * gen_wB w_digits n)) with
    (([|r|] * gen_wB w_digits n + ([!n|hh!] * 2^[|p|] + 
      [!n|hl!] / 2^(Zpos (gen_digits w_digits n) - [|p|])) mod
                      gen_wB w_digits n) * gen_wB w_digits n +
     ([!n|hl!] * 2^[|p|] + 
      [!n|lh!] / 2^(Zpos (gen_digits w_digits n) - [|p|])) mod 
              gen_wB w_digits n).
   generalize (IHn r hh hl H);destruct (gen_divn1_p n r hh hl) as (qh,rh);
   intros (H3,H4);rewrite H3.
   assert ([|rh|] < [|b2p|]). omega. 
   replace (([!n|qh!] * [|b2p|] + [|rh|]) * gen_wB w_digits n +
     ([!n|hl!] * 2 ^ [|p|] +
      [!n|lh!] / 2 ^ (Zpos (gen_digits w_digits n) - [|p|])) mod
      gen_wB w_digits n)  with  
    ([!n|qh!] * [|b2p|] *gen_wB w_digits n + ([|rh|]*gen_wB w_digits n +
      ([!n|hl!] * 2 ^ [|p|] +
       [!n|lh!] / 2 ^ (Zpos (gen_digits w_digits n) - [|p|])) mod
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
   replace (2 ^ (Zpos (gen_digits w_digits (S n)) - [|p|])) with
    (2^(Zpos (gen_digits w_digits n) - [|p|])*2^Zpos (gen_digits w_digits n)).
   rewrite Zdiv_mult_cancel_r;auto with zarith.
   rewrite Zmult_plus_distr_l with (p:=  2^[|p|]). 
   pattern  ([!n|hl!] * 2^[|p|]) at 2;
   rewrite (shift_unshift_mod (Zpos(gen_digits w_digits n))([|p|])([!n|hl!]));
    auto with zarith.
   rewrite Zplus_assoc. 
   replace 
    ([!n|hh!] * 2^Zpos (gen_digits w_digits n)* 2^[|p|] +
      ([!n|hl!] / 2^(Zpos (gen_digits w_digits n)-[|p|])*
       2^Zpos(gen_digits w_digits n)))
   with 
    (([!n|hh!] *2^[|p|] + gen_to_Z w_digits w_to_Z n hl / 
       2^(Zpos (gen_digits w_digits n)-[|p|]))
      * 2^Zpos(gen_digits w_digits n));try (ring;fail).
   rewrite <- Zplus_assoc.
   rewrite <- (Zmod_shift_r ([|p|]));auto with zarith.
   replace 
     (2 ^ Zpos (gen_digits w_digits n) * 2 ^ Zpos (gen_digits w_digits n)) with
     (2 ^ (Zpos (gen_digits w_digits n) + Zpos (gen_digits w_digits n))).
   rewrite (Zmod_shift_r (Zpos (gen_digits w_digits n)));auto with zarith.
   replace (2 ^ (Zpos (gen_digits w_digits n) + Zpos (gen_digits w_digits n)))
   with (2^Zpos(gen_digits w_digits n) *2^Zpos(gen_digits w_digits n)). 
   rewrite (Zmult_comm (([!n|hh!] * 2 ^ [|p|] +
      [!n|hl!] / 2 ^ (Zpos (gen_digits w_digits n) - [|p|])))).
   rewrite  Zmult_mod_distr_l;auto with zarith.
   ring. 
   rewrite Zpower_exp;auto with zarith.
   assert (0 < Zpos (gen_digits w_digits n)). unfold Zlt;reflexivity.
   auto with zarith.
   apply Z_mod_lt;auto with zarith.
   rewrite Zpower_exp;auto with zarith.
   split;auto with zarith.
   apply Zdiv_lt_upper_bound;auto with zarith.
   rewrite <- Zpower_exp;auto with zarith.
   replace ([|p|] + (Zpos (gen_digits w_digits n) - [|p|])) with 
     (Zpos(gen_digits w_digits n));auto with zarith.
   rewrite <- Zpower_exp;auto with zarith.
   replace (Zpos (gen_digits w_digits (S n)) - [|p|]) with 
       (Zpos (gen_digits w_digits n) - [|p|] + 
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

 Fixpoint high (n:nat) : word w n -> w :=
  match n return word w n -> w with
  | O => fun a => a 
  | S n => 
    fun (a:zn2z (word w n)) =>
     match a with
     | W0 => w_0
     | WW h l => high n h
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

 Lemma spec_high : forall n (x:word w n), 
   [|high n x|] = [!n|x!] / 2^(Zpos (gen_digits w_digits n) - Zpos w_digits).
 Proof.
  induction n;intros.
  unfold high,gen_digits,gen_to_Z.
  replace (Zpos w_digits - Zpos w_digits) with 0;try ring.
  simpl. rewrite <- (Zdiv_unique [|x|] 1 [|x|] 0);auto with zarith.
  assert (U2 := spec_gen_digits n). 
  assert (U3 : 0 < Zpos w_digits). exact (refl_equal Lt).
  destruct x;unfold high;fold high.
  unfold gen_to_Z,zn2z_to_Z;rewrite spec_0.
  rewrite Zdiv_0_l;trivial.
  assert (U0 := spec_gen_to_Z w_digits w_to_Z spec_to_Z n w0);
   assert (U1 := spec_gen_to_Z w_digits w_to_Z spec_to_Z n w1).
  simpl [!S n|WW w0 w1!].
  unfold gen_wB,base;rewrite Zdiv_shift_r;auto with zarith.
  replace (2 ^ (Zpos (gen_digits w_digits (S n)) - Zpos w_digits)) with
   (2^(Zpos (gen_digits w_digits n) - Zpos w_digits) * 
        2^Zpos (gen_digits w_digits n)).
  rewrite Zdiv_mult_cancel_r;auto with zarith.
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
  let p := w_head0 b in
  match w_compare p w_0 with
  | Gt =>
    let b2p := w_add_mul_div p b w_0 in
    let ha := high n a in
    let k := w_sub w_zdigits p in
    let lsr_n := w_add_mul_div k w_0 in 
    let r0 := w_add_mul_div p w_0 ha in
    let (q,r) := gen_divn1_p b2p p n r0 a (gen_0 w_0 n) in
    (q, lsr_n r)
  | _ => gen_divn1_0 b n w_0 a 
  end.

 Lemma spec_gen_divn1 : forall n a b,
    0 < [|b|] ->
    let (q,r) := gen_divn1 n a b in
    [!n|a!] = [!n|q!] * [|b|] + [|r|] /\
    0 <= [|r|] < [|b|].
  Proof.
   intros n a b H. unfold gen_divn1.
   case (spec_head0 H); intros H0 H1.
   case (spec_to_Z (w_head0 b)); intros HH1 HH2.
   generalize (spec_compare (w_head0 b) w_0); case w_compare;
     rewrite spec_0; intros H2; auto with zarith.
   assert (Hv1: wB/2 <= [|b|]).
     generalize H0; rewrite H2; rewrite Zpower_0_r;
       rewrite Zmult_1_l; auto.
   assert (Hv2: [|w_0|] < [|b|]).
     rewrite spec_0; auto.
   generalize (spec_gen_divn1_0 Hv1 n a Hv2).
   rewrite spec_0;rewrite Zmult_0_l; rewrite Zplus_0_l; auto.
   contradict H2; auto with zarith.
   assert (HHHH : 0 < [|w_head0 b|]); auto with zarith.
   assert ([|w_head0 b|] < Zpos w_digits).
    case (Zle_or_lt (Zpos w_digits) [|w_head0 b|]); auto; intros HH.
    assert (2 ^ [|w_head0 b|] < wB).
     apply Zle_lt_trans with (2 ^ [|w_head0 b|] * [|b|]);auto with zarith.
     replace (2 ^ [|w_head0 b|]) with (2^[|w_head0 b|] * 1);try (ring;fail).
     apply Zmult_le_compat;auto with zarith.
     assert (wB <= 2^[|w_head0 b|]).
     unfold base;apply Zpower_le_monotone;auto with zarith. omega.
   assert ([|w_add_mul_div (w_head0 b) b w_0|] = 
               2 ^ [|w_head0 b|] * [|b|]).
    rewrite (spec_add_mul_div b w_0); auto with zarith.
    rewrite spec_0;rewrite Zdiv_0_l; try omega.
    rewrite Zplus_0_r; rewrite Zmult_comm.
    rewrite Zmod_small; auto with zarith.
   assert (H5 := spec_to_Z (high n a)).
   assert 
    ([|w_add_mul_div (w_head0 b) w_0 (high n a)|]
          <[|w_add_mul_div (w_head0 b) b w_0|]).
    rewrite H4.
    rewrite spec_add_mul_div;auto with zarith.
    rewrite spec_0;rewrite Zmult_0_l;rewrite Zplus_0_l.
    assert (([|high n a|]/2^(Zpos w_digits - [|w_head0 b|])) < wB).
     apply Zdiv_lt_upper_bound;auto with zarith. 
     apply Zlt_le_trans with wB;auto with zarith.
     pattern wB at 1;replace wB with (wB*1);try ring.
     apply Zmult_le_compat;auto with zarith.
     assert (H6 := Zpower_gt_0 2 (Zpos w_digits - [|w_head0 b|]));
       auto with zarith.
    rewrite Zmod_small;auto with zarith.
    apply Zdiv_lt_upper_bound;auto with zarith.
    apply Zlt_le_trans with wB;auto with zarith.
    apply Zle_trans with (2 ^ [|w_head0 b|] * [|b|] * 2).
    rewrite <- wB_div_2; try omega.
    apply Zmult_le_compat;auto with zarith.
    pattern 2 at 1;rewrite <- Zpower_1_r.
    apply Zpower_le_monotone;split;auto with zarith.
   rewrite <- H4 in H0. 
   assert (Hb3: [|w_head0 b|] <= Zpos w_digits); auto with zarith. 
   assert (H7:= spec_gen_divn1_p H0 Hb3 n a (gen_0 w_0 n) H6).
   destruct (gen_divn1_p (w_add_mul_div (w_head0 b) b w_0) (w_head0 b) n
             (w_add_mul_div (w_head0 b) w_0 (high n a)) a
             (gen_0 w_0 n)) as (q,r).
   assert (U:= spec_gen_digits n).
   rewrite spec_gen_0 in H7;trivial;rewrite Zdiv_0_l in H7.
   rewrite Zplus_0_r in H7.
   rewrite spec_add_mul_div in H7;auto with zarith.
   rewrite spec_0 in H7;rewrite Zmult_0_l in H7;rewrite Zplus_0_l in H7.
   assert (([|high n a|] / 2 ^ (Zpos w_digits - [|w_head0 b|])) mod wB
     = [!n|a!] / 2^(Zpos (gen_digits w_digits n) - [|w_head0 b|])).
   rewrite Zmod_small;auto with zarith.
   rewrite spec_high. rewrite Zdiv_Zdiv;auto with zarith.
   rewrite <- Zpower_exp;auto with zarith.
   replace (Zpos (gen_digits w_digits n) - Zpos w_digits + 
                       (Zpos w_digits - [|w_head0 b|]))
    with (Zpos (gen_digits w_digits n) - [|w_head0 b|]);trivial;ring.
   assert (H8 := Zpower_gt_0 2  (Zpos w_digits - [|w_head0 b|]));auto with zarith.
   split;auto with zarith.
   apply Zle_lt_trans with ([|high n a|]);auto with zarith.
   apply Zdiv_le_upper_bound;auto with zarith.
   pattern ([|high n a|]) at 1;rewrite <- Zmult_1_r.
   apply Zmult_le_compat;auto with zarith.
   rewrite H8 in H7;unfold gen_wB,base in H7.
   rewrite <- shift_unshift_mod in H7;auto with zarith.
   rewrite H4 in H7.
   assert ([|w_add_mul_div (w_sub w_zdigits (w_head0 b)) w_0 r|] 
               = [|r|]/2^[|w_head0 b|]).
   rewrite spec_add_mul_div.
   rewrite spec_0;rewrite Zmult_0_l;rewrite Zplus_0_l.
   replace (Zpos w_digits - [|w_sub w_zdigits (w_head0 b)|]) 
      with ([|w_head0 b|]).
   rewrite Zmod_small;auto with zarith.
   assert (H9 := spec_to_Z r).
   split;auto with zarith.
   apply Zle_lt_trans with ([|r|]);auto with zarith.
   apply Zdiv_le_upper_bound;auto with zarith.
   pattern ([|r|]) at 1;rewrite <- Zmult_1_r.
   apply Zmult_le_compat;auto with zarith.
   assert (H10 := Zpower_gt_0 2  ([|w_head0 b|]));auto with zarith.
   rewrite spec_sub.
   rewrite Zmod_small; auto with zarith.
   split; auto with zarith.
   case (spec_to_Z w_zdigits); auto with zarith.
   rewrite spec_sub.
   rewrite Zmod_small; auto with zarith.
   split; auto with zarith.
   case (spec_to_Z w_zdigits); auto with zarith.
  case H7; intros H71 H72.
   split.
   rewrite <- (Z_div_mult [!n|a!] (2^[|w_head0 b|]));auto with zarith.
   rewrite H71;rewrite H9.
   replace ([!n|q!] * (2 ^ [|w_head0 b|] * [|b|])) 
      with ([!n|q!] *[|b|] * 2^[|w_head0 b|]);
     try (ring;fail).
   rewrite Z_div_plus_l;auto with zarith.
   assert (H10 := spec_to_Z 
       (w_add_mul_div (w_sub w_zdigits (w_head0 b)) w_0 r));split;
    auto with zarith.
   rewrite H9.
   apply Zdiv_lt_upper_bound;auto with zarith.
   rewrite Zmult_comm;auto with zarith.
   exact (spec_gen_to_Z w_digits w_to_Z spec_to_Z n a).
 Qed.

 
 Definition gen_modn1 (n:nat) (a:word w n) (b:w) := 
  let p := w_head0 b in
  match w_compare p w_0 with
  | Gt =>
    let b2p := w_add_mul_div p b w_0 in
    let ha := high n a in
    let k := w_sub w_zdigits p in
    let lsr_n := w_add_mul_div k w_0 in 
    let r0 := w_add_mul_div p w_0 ha in
    let r := gen_modn1_p b2p p n r0 a (gen_0 w_0 n) in
    lsr_n r
  | _ => gen_modn1_0 b n w_0 a 
  end.

 Lemma spec_gen_modn1_aux : forall n a b,
    gen_modn1 n a b = snd (gen_divn1 n a b).
 Proof.
  intros n a b;unfold gen_divn1,gen_modn1.
  generalize (spec_compare (w_head0 b) w_0); case w_compare;
     rewrite spec_0; intros H2; auto with zarith.
  apply spec_gen_modn1_0.
  apply spec_gen_modn1_0.
  rewrite spec_gen_modn1_p.
  destruct (gen_divn1_p (w_add_mul_div (w_head0 b) b w_0) (w_head0 b) n
            (w_add_mul_div (w_head0 b) w_0 (high n a)) a (gen_0 w_0 n));simpl;trivial.
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
