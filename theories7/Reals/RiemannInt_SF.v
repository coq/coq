(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
 
(*i $Id$ i*)

Require Rbase.
Require Rfunctions.
Require Ranalysis.
Require Classical_Prop.
V7only [ Import nat_scope. Import Z_scope. Import R_scope. ].
Open Local Scope R_scope.

Implicit Arguments On.

(**************************************************)
(* Each bounded subset of N has a maximal element *)
(**************************************************)

Definition Nbound [I:nat->Prop] : Prop := (EX n:nat | (i:nat)(I i)->(le i n)).

Lemma IZN_var:(z:Z)(`0<=z`)->{ n:nat | z=(INZ n)}.
Intros; Apply inject_nat_complete_inf; Assumption.
Qed.

Lemma Nzorn : (I:nat->Prop) (EX n:nat | (I n)) -> (Nbound I) -> (sigTT ?  [n:nat](I n)/\(i:nat)(I i)->(le i n)).
Intros I H H0; Pose E := [x:R](EX i:nat | (I i)/\(INR i)==x); Assert H1 : (bound E).
Unfold Nbound in H0; Elim H0; Intros N H1; Unfold bound; Exists (INR N); Unfold is_upper_bound; Intros; Unfold E in H2; Elim H2; Intros; Elim H3; Intros; Rewrite <- H5; Apply le_INR; Apply H1; Assumption.
Assert H2 : (EXT x:R | (E x)).
Elim H; Intros; Exists (INR x); Unfold E; Exists x; Split; [Assumption | Reflexivity].
Assert H3 := (complet E H1 H2); Elim H3; Intros; Unfold is_lub in p; Elim p; Clear p; Intros; Unfold is_upper_bound in H4 H5; Assert H6 : ``0<=x``.
Elim H2; Intros; Unfold E in H6; Elim H6; Intros; Elim H7; Intros; Apply Rle_trans with x0; [Rewrite <- H9; Change ``(INR O)<=(INR x1)``; Apply le_INR; Apply le_O_n | Apply H4; Assumption].
Assert H7 := (archimed x); Elim H7; Clear H7; Intros; Assert H9 : ``x<=(IZR (up x))-1``.
Apply H5; Intros; Assert H10 := (H4 ? H9); Unfold E in H9; Elim H9; Intros; Elim H11; Intros; Rewrite <- H13; Apply Rle_anti_compatibility with R1; Replace ``1+((IZR (up x))-1)`` with (IZR (up x)); [Idtac | Ring]; Replace ``1+(INR x1)`` with (INR (S x1)); [Idtac | Rewrite S_INR; Ring].
Assert H14 : `0<=(up x)`.
Apply le_IZR; Apply Rle_trans with x; [Apply H6 | Left; Assumption].
Assert H15 := (IZN ? H14); Elim H15; Clear H15; Intros; Rewrite H15; Rewrite <- INR_IZR_INZ; Apply le_INR; Apply lt_le_S; Apply INR_lt; Rewrite H13; Apply Rle_lt_trans with x; [Assumption | Rewrite INR_IZR_INZ; Rewrite <- H15; Assumption].
Assert H10 : ``x==(IZR (up x))-1``.
Apply Rle_antisym; [Assumption | Apply Rle_anti_compatibility with ``-x+1``; Replace `` -x+1+((IZR (up x))-1)`` with ``(IZR (up x))-x``; [Idtac | Ring]; Replace ``-x+1+x`` with R1; [Assumption | Ring]].
Assert H11 : `0<=(up x)`.
Apply le_IZR; Apply Rle_trans with x; [Apply H6 | Left; Assumption].
Assert H12 := (IZN_var H11); Elim H12; Clear H12; Intros; Assert H13 : (E x).
Elim (classic (E x)); Intro; Try Assumption.
Cut ((y:R)(E y)->``y<=x-1``).
Intro; Assert H14 := (H5 ? H13); Cut ``x-1<x``.
Intro; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H14 H15)).
Apply Rminus_lt; Replace ``x-1-x`` with ``-1``; [Idtac | Ring]; Rewrite <- Ropp_O; Apply Rlt_Ropp; Apply Rlt_R0_R1.
Intros; Assert H14 := (H4 ? H13); Elim H14; Intro; Unfold E in H13; Elim H13; Intros; Elim H16; Intros; Apply Rle_anti_compatibility with R1.
Replace ``1+(x-1)`` with x; [Idtac | Ring]; Rewrite <- H18; Replace ``1+(INR x1)`` with (INR (S x1)); [Idtac | Rewrite S_INR; Ring].
Cut x==(INR (pred x0)).
Intro; Rewrite H19; Apply le_INR; Apply lt_le_S; Apply INR_lt; Rewrite H18; Rewrite <- H19; Assumption.
Rewrite H10; Rewrite p; Rewrite <- INR_IZR_INZ; Replace R1 with (INR (S O)); [Idtac | Reflexivity]; Rewrite <- minus_INR.
Replace (minus x0 (S O)) with (pred x0); [Reflexivity | Case x0; [Reflexivity | Intro; Simpl; Apply minus_n_O]].
Induction x0; [Rewrite p in H7; Rewrite <- INR_IZR_INZ in H7; Simpl in H7; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H6 H7)) | Apply le_n_S; Apply le_O_n].
Rewrite H15 in H13; Elim H12; Assumption.
Split with (pred x0); Unfold E in H13; Elim H13; Intros; Elim H12; Intros; Rewrite H10 in H15; Rewrite p in H15; Rewrite <- INR_IZR_INZ in H15; Assert H16 : ``(INR x0)==(INR x1)+1``.
Rewrite H15; Ring.
Rewrite <- S_INR in H16; Assert H17 := (INR_eq ? ? H16); Rewrite H17; Simpl; Split.
Assumption.
Intros; Apply INR_le; Rewrite H15; Rewrite <- H15; Elim H12; Intros; Rewrite H20; Apply H4; Unfold E; Exists i; Split; [Assumption | Reflexivity].
Qed.

(*******************************************)
(*             Step functions              *)
(*******************************************)

Definition open_interval [a,b:R] : R->Prop := [x:R]``a<x<b``.
Definition co_interval [a,b:R] : R->Prop := [x:R]``a<=x<b``. 

Definition adapted_couple [f:R->R;a,b:R;l,lf:Rlist] : Prop := (ordered_Rlist l)/\``(pos_Rl l O)==(Rmin a b)``/\``(pos_Rl l (pred (Rlength l)))==(Rmax a b)``/\(Rlength l)=(S (Rlength lf))/\(i:nat)(lt i (pred (Rlength l)))->(constant_D_eq f (open_interval (pos_Rl l i) (pos_Rl l (S i))) (pos_Rl lf i)).

Definition adapted_couple_opt [f:R->R;a,b:R;l,lf:Rlist] := (adapted_couple f a b l lf)/\((i:nat)(lt i (pred (Rlength lf)))->(``(pos_Rl lf i)<>(pos_Rl lf (S i))``\/``(f (pos_Rl l (S i)))<>(pos_Rl lf i)``))/\((i:nat)(lt i (pred (Rlength l)))->``(pos_Rl l i)<>(pos_Rl l (S i))``).

Definition is_subdivision [f:R->R;a,b:R;l:Rlist] : Type := (sigTT ? [l0:Rlist](adapted_couple f a b l l0)).

Definition IsStepFun [f:R->R;a,b:R] : Type := (SigT ? [l:Rlist](is_subdivision f a b l)).

(* Class of step functions *)
Record StepFun [a,b:R] : Type := mkStepFun {
  fe:> R->R;
  pre:(IsStepFun fe a b)}.

Definition subdivision [a,b:R;f:(StepFun a b)] : Rlist := (projT1 ? ? (pre f)).

Definition subdivision_val [a,b:R;f:(StepFun a b)] : Rlist := Cases (projT2 ? ? (pre f)) of (existTT a b) => a end.

Fixpoint Int_SF [l:Rlist] : Rlist -> R :=
[k:Rlist] Cases l of
| nil => R0
| (cons a l') => Cases k of
   | nil => R0
   | (cons x nil) => R0
   | (cons x (cons y k')) => ``a*(y-x)+(Int_SF l' (cons y k'))``
  end
end.

(* Integral of step functions *)
Definition RiemannInt_SF [a,b:R;f:(StepFun a b)] : R := 
Cases (total_order_Rle a b) of
  (leftT _) => (Int_SF (subdivision_val f) (subdivision f))
| (rightT _) => ``-(Int_SF (subdivision_val f) (subdivision f))``
end.

(********************************)
(* Properties of step functions *)
(********************************)

Lemma StepFun_P1 : (a,b:R;f:(StepFun a b)) (adapted_couple f a b (subdivision f) (subdivision_val f)).
Intros a b f; Unfold subdivision_val; Case (projT2 Rlist ([l:Rlist](is_subdivision f a b l)) (pre f)); Intros; Apply a0.
Qed.

Lemma StepFun_P2 : (a,b:R;f:R->R;l,lf:Rlist) (adapted_couple f a b l lf) -> (adapted_couple f b a l lf).
Unfold adapted_couple; Intros; Decompose [and] H; Clear H; Repeat Split; Try Assumption.
Rewrite H2; Unfold Rmin; Case (total_order_Rle a b); Intro; Case (total_order_Rle b a); Intro; Try Reflexivity.
Apply Rle_antisym; Assumption.
Apply Rle_antisym; Auto with real.
Rewrite H1; Unfold Rmax; Case (total_order_Rle a b); Intro; Case (total_order_Rle b a); Intro; Try Reflexivity.
Apply Rle_antisym; Assumption.
Apply Rle_antisym; Auto with real.
Qed.

Lemma StepFun_P3 : (a,b,c:R) ``a<=b`` -> (adapted_couple (fct_cte c) a b (cons a (cons b nil)) (cons c nil)).
Intros; Unfold adapted_couple; Repeat Split.
Unfold ordered_Rlist; Intros; Simpl in H0; Inversion H0; [Simpl; Assumption | Elim (le_Sn_O ? H2)].
Simpl; Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Simpl; Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Unfold constant_D_eq open_interval; Intros; Simpl in H0; Inversion H0; [Reflexivity | Elim (le_Sn_O ? H3)].
Qed.

Lemma StepFun_P4 : (a,b,c:R) (IsStepFun (fct_cte c) a b).
Intros; Unfold IsStepFun; Case (total_order_Rle a b); Intro.
Apply Specif.existT with (cons a (cons b nil)); Unfold is_subdivision; Apply existTT with (cons c nil); Apply (StepFun_P3 c r).
Apply Specif.existT with (cons b (cons a nil)); Unfold is_subdivision; Apply existTT with (cons c nil); Apply StepFun_P2; Apply StepFun_P3; Auto with real.
Qed.

Lemma StepFun_P5 : (a,b:R;f:R->R;l:Rlist) (is_subdivision f a b l) -> (is_subdivision f b a l).
Unfold is_subdivision; Intros; Elim X; Intros; Exists x; Unfold adapted_couple in p; Decompose [and] p; Clear p; Unfold adapted_couple; Repeat Split; Try Assumption.
Rewrite H1; Unfold Rmin; Case (total_order_Rle a b); Intro; Case (total_order_Rle b a); Intro; Try Reflexivity.
Apply Rle_antisym; Assumption.
Apply Rle_antisym; Auto with real.
Rewrite H0; Unfold Rmax; Case (total_order_Rle a b); Intro; Case (total_order_Rle b a); Intro; Try Reflexivity.
Apply Rle_antisym; Assumption.
Apply Rle_antisym; Auto with real.
Qed.

Lemma StepFun_P6 : (f:R->R;a,b:R) (IsStepFun f a b) -> (IsStepFun f b a).
Unfold IsStepFun; Intros; Elim X; Intros; Apply Specif.existT with x; Apply StepFun_P5; Assumption.
Qed.

Lemma StepFun_P7 : (a,b,r1,r2,r3:R;f:R->R;l,lf:Rlist) ``a<=b`` -> (adapted_couple f a b (cons r1 (cons r2 l)) (cons r3 lf)) -> (adapted_couple f r2 b (cons r2 l) lf).
Unfold adapted_couple; Intros; Decompose [and] H0; Clear H0; Assert H5 : (Rmax a b)==b.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Assert H7 : ``r2<=b``.
Rewrite H5 in H2; Rewrite <- H2; Apply RList_P7; [Assumption | Simpl; Right; Left; Reflexivity].
Repeat Split.
Apply RList_P4 with r1; Assumption.
Rewrite H5 in H2; Unfold Rmin; Case (total_order_Rle r2 b); Intro; [Reflexivity | Elim n; Assumption].
Unfold Rmax; Case (total_order_Rle r2 b); Intro; [Rewrite H5 in H2; Rewrite <- H2; Reflexivity | Elim n; Assumption].
Simpl in H4; Simpl; Apply INR_eq; Apply r_Rplus_plus with R1; Do 2 Rewrite (Rplus_sym R1); Do 2 Rewrite <- S_INR; Rewrite H4; Reflexivity.
Intros; Unfold constant_D_eq open_interval; Intros; Unfold constant_D_eq open_interval in H6; Assert H9 : (lt (S i) (pred (Rlength (cons r1 (cons r2 l))))).
Simpl; Simpl in H0; Apply lt_n_S; Assumption.
Assert H10 := (H6 ? H9); Apply H10; Assumption.
Qed.

Lemma StepFun_P8 : (f:R->R;l1,lf1:Rlist;a,b:R) (adapted_couple f a b l1 lf1) -> a==b -> (Int_SF lf1 l1)==R0.
Induction l1.
Intros; Induction lf1; Reflexivity.
Induction r0.
Intros; Induction lf1.
Reflexivity.
Unfold adapted_couple in H0; Decompose [and] H0; Clear H0; Simpl in H5; Discriminate.
Intros; Induction lf1.
Reflexivity.
Simpl; Cut r==r1.
Intro; Rewrite H3; Rewrite (H0 lf1 r b).
Ring.
Rewrite H3; Apply StepFun_P7 with a r r3; [Right; Assumption | Assumption].
Clear H H0 Hreclf1 r0; Unfold adapted_couple in H1; Decompose [and] H1; Intros; Simpl in H4; Rewrite H4; Unfold Rmin; Case (total_order_Rle a b); Intro; [Assumption | Reflexivity].
Unfold adapted_couple in H1; Decompose [and] H1; Intros; Apply Rle_antisym.
Apply (H3 O); Simpl; Apply lt_O_Sn.
Simpl in H5; Rewrite H2 in H5; Rewrite H5; Replace (Rmin b b) with (Rmax a b); [Rewrite <- H4; Apply RList_P7; [Assumption | Simpl; Right; Left; Reflexivity] | Unfold Rmin Rmax; Case (total_order_Rle b b); Case (total_order_Rle a b); Intros; Try Assumption Orelse Reflexivity].
Qed.

Lemma StepFun_P9 : (a,b:R;f:R->R;l,lf:Rlist) (adapted_couple f a b l lf) -> ``a<>b`` -> (le (2) (Rlength l)).
Intros; Unfold adapted_couple in H; Decompose [and] H; Clear H; Induction l; [Simpl in H4; Discriminate | Induction l; [Simpl in H3; Simpl in H2; Generalize H3; Generalize H2; Unfold Rmin Rmax; Case (total_order_Rle a b); Intros; Elim H0; Rewrite <- H5; Rewrite <- H7; Reflexivity | Simpl; Do 2 Apply le_n_S; Apply le_O_n]].
Qed.

Lemma StepFun_P10 : (f:R->R;l,lf:Rlist;a,b:R) ``a<=b`` -> (adapted_couple f a b l lf) -> (EXT l':Rlist | (EXT lf':Rlist | (adapted_couple_opt f a b l' lf'))).
Induction l.
Intros; Unfold adapted_couple in H0; Decompose [and] H0; Simpl in H4; Discriminate.
Intros; Case (Req_EM a b); Intro.
Exists (cons a nil); Exists nil; Unfold adapted_couple_opt; Unfold adapted_couple; Unfold ordered_Rlist; Repeat Split; Try (Intros; Simpl in H3; Elim (lt_n_O ? H3)).
Simpl; Rewrite <- H2; Unfold Rmin; Case (total_order_Rle a a); Intro; Reflexivity.
Simpl; Rewrite <- H2; Unfold Rmax; Case (total_order_Rle a a); Intro; Reflexivity.
Elim (RList_P20 ? (StepFun_P9 H1 H2)); Intros t1 [t2 [t3 H3]]; Induction lf.
Unfold adapted_couple in H1; Decompose [and] H1; Rewrite H3 in H7; Simpl in H7; Discriminate.
Clear Hreclf; Assert H4 : (adapted_couple f t2 b r0 lf).
Rewrite H3 in H1; Assert H4 := (RList_P21 ? ? H3); Simpl in H4; Rewrite H4; EApply StepFun_P7; [Apply H0 | Apply H1].
Cut ``t2<=b``.
Intro; Assert H6 := (H ? ? ? H5 H4); Case (Req_EM t1 t2); Intro Hyp_eq.
Replace a with t2.
Apply H6.
Rewrite <- Hyp_eq; Rewrite H3 in H1; Unfold adapted_couple in H1; Decompose [and] H1; Clear H1; Simpl in H9; Rewrite H9; Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Elim H6; Clear H6; Intros l' [lf' H6]; Case (Req_EM t2 b); Intro.
Exists (cons a (cons b nil)); Exists (cons r1 nil); Unfold adapted_couple_opt; Unfold adapted_couple; Repeat Split.
Unfold ordered_Rlist; Intros; Simpl in H8; Inversion H8; [Simpl; Assumption | Elim (le_Sn_O ? H10)].
Simpl; Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Simpl; Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Intros; Simpl in H8; Inversion H8.
Unfold constant_D_eq open_interval; Intros; Simpl; Simpl in H9; Rewrite H3 in H1; Unfold adapted_couple in H1; Decompose [and] H1; Apply (H16 O).
Simpl; Apply lt_O_Sn.
Unfold open_interval; Simpl; Rewrite H7; Simpl in H13; Rewrite H13; Unfold Rmin; Case (total_order_Rle a b); Intro; [Assumption | Elim n; Assumption].
Elim (le_Sn_O ? H10).
Intros; Simpl in H8; Elim (lt_n_O ? H8).
Intros; Simpl in H8; Inversion H8; [Simpl; Assumption | Elim (le_Sn_O ? H10)].
Assert Hyp_min : (Rmin t2 b)==t2.
Unfold Rmin; Case (total_order_Rle t2 b); Intro; [Reflexivity | Elim n; Assumption].
Unfold adapted_couple in H6; Elim H6; Clear H6; Intros; Elim (RList_P20 ? (StepFun_P9 H6 H7)); Intros s1 [s2 [s3 H9]]; Induction lf'.
Unfold adapted_couple in H6; Decompose [and] H6; Rewrite H9 in H13; Simpl in H13; Discriminate.
Clear Hreclf'; Case (Req_EM r1 r2); Intro.
Case (Req_EM (f t2) r1); Intro.
Exists (cons t1 (cons s2 s3)); Exists (cons r1 lf'); Rewrite H3 in H1; Rewrite H9 in H6; Unfold adapted_couple in H6 H1; Decompose [and] H1; Decompose [and] H6; Clear H1 H6; Unfold adapted_couple_opt; Unfold adapted_couple; Repeat Split.
Unfold ordered_Rlist; Intros; Simpl in H1; Induction i.
Simpl; Apply Rle_trans with s1.
Replace s1 with t2.
Apply (H12 O).
Simpl; Apply lt_O_Sn.
Simpl in H19; Rewrite H19; Symmetry; Apply Hyp_min.
Apply (H16 O); Simpl; Apply lt_O_Sn.
Change ``(pos_Rl (cons s2 s3) i)<=(pos_Rl (cons s2 s3) (S i))``; Apply (H16 (S i)); Simpl; Assumption.
Simpl; Simpl in H14; Rewrite H14; Reflexivity.
Simpl; Simpl in H18; Rewrite H18; Unfold Rmax; Case (total_order_Rle a b); Case (total_order_Rle t2 b); Intros; Reflexivity Orelse Elim n; Assumption.
Simpl; Simpl in H20; Apply H20.
Intros; Simpl in H1; Unfold constant_D_eq open_interval; Intros; Induction i.
Simpl; Simpl in H6; Case (total_order_T x t2); Intro.
Elim s; Intro.
Apply (H17 O); [Simpl; Apply lt_O_Sn | Unfold open_interval; Simpl; Elim H6; Intros; Split; Assumption].
Rewrite b0; Assumption.
Rewrite H10; Apply (H22 O); [Simpl; Apply lt_O_Sn | Unfold open_interval; Simpl; Replace s1 with t2; [Elim H6; Intros; Split; Assumption | Simpl in H19; Rewrite H19; Rewrite Hyp_min; Reflexivity]].
Simpl; Simpl in H6; Apply (H22 (S i)); [Simpl; Assumption | Unfold open_interval; Simpl; Apply H6].
Intros; Simpl in H1; Rewrite H10; Change ``(pos_Rl (cons r2 lf') i)<>(pos_Rl (cons r2 lf') (S i))``\/``(f (pos_Rl (cons s1 (cons s2 s3)) (S i)))<>(pos_Rl (cons r2 lf') i)``; Rewrite <- H9; Elim H8; Intros; Apply H6; Simpl; Apply H1.
Intros; Induction i.
Simpl; Red; Intro; Elim Hyp_eq; Apply Rle_antisym.
Apply (H12 O); Simpl; Apply lt_O_Sn.
Rewrite <- Hyp_min; Rewrite H6; Simpl in H19; Rewrite <- H19; Apply (H16 O); Simpl; Apply lt_O_Sn.
Elim H8; Intros; Rewrite H9 in H21; Apply (H21 (S i)); Simpl; Simpl in H1; Apply H1.
Exists (cons t1 l'); Exists (cons r1 (cons r2 lf')); Rewrite H9 in H6; Rewrite H3 in H1; Unfold adapted_couple in H1 H6; Decompose [and] H6; Decompose [and] H1; Clear H6 H1; Unfold adapted_couple_opt; Unfold adapted_couple; Repeat Split.
Rewrite H9; Unfold ordered_Rlist; Intros; Simpl in H1; Induction i.
Simpl; Replace s1 with t2.
Apply (H16 O); Simpl; Apply lt_O_Sn.
Simpl in H14; Rewrite H14; Rewrite Hyp_min; Reflexivity.
Change ``(pos_Rl (cons s1 (cons s2 s3)) i)<=(pos_Rl (cons s1 (cons s2 s3)) (S i))``; Apply (H12 i); Simpl; Apply lt_S_n; Assumption.
Simpl; Simpl in H19; Apply H19.
Rewrite H9; Simpl; Simpl in H13; Rewrite H13; Unfold Rmax; Case (total_order_Rle t2 b); Case (total_order_Rle a b); Intros; Reflexivity Orelse Elim n; Assumption.
Rewrite H9; Simpl; Simpl in H15; Rewrite H15; Reflexivity.
Intros; Simpl in H1; Unfold constant_D_eq open_interval; Intros; Induction i.
Simpl; Rewrite H9 in H6; Simpl in H6; Apply (H22 O).
Simpl; Apply lt_O_Sn.
Unfold open_interval; Simpl.
Replace t2 with s1.
Assumption.
Simpl in H14; Rewrite H14; Rewrite Hyp_min; Reflexivity.
Change (f x)==(pos_Rl (cons r2 lf') i); Clear Hreci; Apply (H17 i).
Simpl; Rewrite H9 in H1; Simpl in H1; Apply lt_S_n; Apply H1.
Rewrite H9 in H6; Unfold open_interval; Apply H6.
Intros; Simpl in H1; Induction i.
Simpl; Rewrite H9; Right; Simpl; Replace s1 with t2.
Assumption.
Simpl in H14; Rewrite H14; Rewrite Hyp_min; Reflexivity.
Elim H8; Intros; Apply (H6 i).
Simpl; Apply lt_S_n; Apply H1.
Intros; Rewrite H9; Induction i.
Simpl; Red; Intro; Elim Hyp_eq; Apply Rle_antisym.
Apply (H16 O); Simpl; Apply lt_O_Sn.
Rewrite <- Hyp_min; Rewrite H6; Simpl in H14; Rewrite <- H14; Right; Reflexivity.
Elim H8; Intros; Rewrite <- H9; Apply (H21 i); Rewrite H9; Rewrite H9 in H1; Simpl; Simpl in H1; Apply lt_S_n; Apply H1.
Exists (cons t1 l'); Exists (cons r1 (cons r2 lf')); Rewrite H9 in H6; Rewrite H3 in H1; Unfold adapted_couple in H1 H6; Decompose [and] H6; Decompose [and] H1; Clear H6 H1; Unfold adapted_couple_opt; Unfold adapted_couple; Repeat Split.
Rewrite H9; Unfold ordered_Rlist; Intros; Simpl in H1; Induction i.
Simpl; Replace s1 with t2.
Apply (H15 O); Simpl; Apply lt_O_Sn.
Simpl in H13; Rewrite H13; Rewrite Hyp_min; Reflexivity.
Change ``(pos_Rl (cons s1 (cons s2 s3)) i)<=(pos_Rl (cons s1 (cons s2 s3)) (S i))``; Apply (H11 i); Simpl; Apply lt_S_n; Assumption.
Simpl; Simpl in H18; Apply H18.
Rewrite H9; Simpl; Simpl in H12; Rewrite H12; Unfold Rmax; Case (total_order_Rle t2 b); Case (total_order_Rle a b); Intros; Reflexivity Orelse Elim n; Assumption.
Rewrite H9; Simpl; Simpl in H14; Rewrite H14; Reflexivity.
Intros; Simpl in H1; Unfold constant_D_eq open_interval; Intros; Induction i.
Simpl; Rewrite H9 in H6; Simpl in H6; Apply (H21 O).
Simpl; Apply lt_O_Sn.
Unfold open_interval; Simpl; Replace t2 with s1.
Assumption.
Simpl in H13; Rewrite H13; Rewrite Hyp_min; Reflexivity.
Change (f x)==(pos_Rl (cons r2 lf') i); Clear Hreci; Apply (H16 i).
Simpl; Rewrite H9 in H1; Simpl in H1; Apply lt_S_n; Apply H1.
Rewrite H9 in H6; Unfold open_interval; Apply H6.
Intros; Simpl in H1; Induction i.
Simpl; Left; Assumption.
Elim H8; Intros; Apply (H6 i).
Simpl; Apply lt_S_n; Apply H1.
Intros; Rewrite H9; Induction i.
Simpl; Red; Intro; Elim Hyp_eq; Apply Rle_antisym.
Apply (H15 O); Simpl; Apply lt_O_Sn.
Rewrite <- Hyp_min; Rewrite H6; Simpl in H13; Rewrite <- H13; Right; Reflexivity.
Elim H8; Intros; Rewrite <- H9; Apply (H20 i); Rewrite H9; Rewrite H9 in H1; Simpl; Simpl in H1; Apply lt_S_n; Apply H1.
Rewrite H3 in H1; Clear H4; Unfold adapted_couple in H1; Decompose [and] H1; Clear H1; Clear H H7 H9; Cut (Rmax a b)==b; [Intro; Rewrite H in H5; Rewrite <- H5; Apply RList_P7; [Assumption | Simpl; Right; Left; Reflexivity] | Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption]].
Qed.

Lemma StepFun_P11 : (a,b,r,r1,r3,s1,s2,r4:R;r2,lf1,s3,lf2:Rlist;f:R->R) ``a<b`` -> (adapted_couple f a b (cons r (cons r1 r2)) (cons r3 lf1)) -> (adapted_couple_opt f a b (cons s1 (cons s2 s3)) (cons r4 lf2)) -> ``r1<=s2``.
Intros; Unfold adapted_couple_opt in H1; Elim H1; Clear H1; Intros; Unfold adapted_couple in H0 H1; Decompose [and] H0; Decompose [and] H1; Clear H0 H1; Assert H12 : r==s1.
Simpl in H10; Simpl in H5; Rewrite H10; Rewrite H5; Reflexivity.
Assert H14 := (H3 O (lt_O_Sn ?)); Simpl in H14; Elim H14; Intro.
Assert H15 := (H7 O (lt_O_Sn ?)); Simpl in H15; Elim H15; Intro.
Rewrite <- H12 in H1; Case (total_order_Rle r1 s2); Intro; Try Assumption.
Assert H16 : ``s2<r1``; Auto with real.
Induction s3.
Simpl in H9; Rewrite H9 in H16; Cut ``r1<=(Rmax a b)``.
Intro; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H17 H16)).
Rewrite <- H4; Apply RList_P7; [Assumption | Simpl; Right; Left; Reflexivity].
Clear Hrecs3; Induction lf2.
Simpl in H11; Discriminate.
Clear Hreclf2; Assert H17 : r3==r4.
Pose x := ``(r+s2)/2``; Assert H17 := (H8 O (lt_O_Sn ?)); Assert H18 := (H13 O (lt_O_Sn ?)); Unfold constant_D_eq open_interval in H17 H18; Simpl in H17; Simpl in H18; Rewrite <- (H17 x).
Rewrite <- (H18 x).
Reflexivity.
Rewrite <- H12; Unfold x; Split.
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Apply Rlt_compatibility; Assumption | DiscrR]].
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite (Rplus_sym r); Rewrite double; Apply Rlt_compatibility; Assumption | DiscrR]].
Unfold x; Split.
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Apply Rlt_compatibility; Assumption | DiscrR]].
Apply Rlt_trans with s2; [Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite (Rplus_sym r); Rewrite double; Apply Rlt_compatibility; Assumption | DiscrR]] | Assumption].
Assert H18 : (f s2)==r3.
Apply (H8 O); [Simpl; Apply lt_O_Sn | Unfold open_interval; Simpl; Split; Assumption].
Assert H19 : r3 == r5.
Assert H19 := (H7 (S O)); Simpl in H19; Assert H20 := (H19 (lt_n_S ? ? (lt_O_Sn ?))); Elim H20; Intro.
Pose x := ``(s2+(Rmin r1 r0))/2``; Assert H22 := (H8 O); Assert H23 := (H13 (S O)); Simpl in H22; Simpl in H23; Rewrite <- (H22 (lt_O_Sn ?) x).
Rewrite <- (H23 (lt_n_S ? ? (lt_O_Sn ?)) x).
Reflexivity.
Unfold open_interval; Simpl; Unfold x; Split.
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Apply Rlt_compatibility; Unfold Rmin; Case (total_order_Rle r1 r0); Intro; Assumption | DiscrR]].
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Apply Rlt_le_trans with ``r0+(Rmin r1 r0)``; [Do 2 Rewrite <- (Rplus_sym (Rmin r1 r0)); Apply Rlt_compatibility; Assumption | Apply Rle_compatibility; Apply Rmin_r] | DiscrR]].
Unfold open_interval; Simpl; Unfold x; Split.
Apply Rlt_trans with s2; [Assumption | Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Apply Rlt_compatibility; Unfold Rmin; Case (total_order_Rle r1 r0); Intro; Assumption | DiscrR]]].
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Apply Rlt_le_trans with ``r1+(Rmin r1 r0)``; [Do 2 Rewrite <- (Rplus_sym (Rmin r1 r0)); Apply Rlt_compatibility; Assumption | Apply Rle_compatibility; Apply Rmin_l] | DiscrR]].
Elim H2; Clear H2; Intros; Assert H23 := (H22 (S O)); Simpl in H23; Assert H24 := (H23 (lt_n_S ? ? (lt_O_Sn ?))); Elim H24; Assumption.
Elim H2; Intros; Assert H22 := (H20 O); Simpl in H22; Assert H23 := (H22 (lt_O_Sn ?)); Elim H23; Intro; [Elim H24; Rewrite <- H17; Rewrite <- H19; Reflexivity | Elim H24; Rewrite <- H17; Assumption].
Elim H2; Clear H2; Intros; Assert H17 := (H16 O); Simpl in H17; Elim (H17 (lt_O_Sn ?)); Assumption.
Rewrite <- H0; Rewrite H12; Apply (H7 O); Simpl; Apply lt_O_Sn.
Qed.

Lemma StepFun_P12 : (a,b:R;f:R->R;l,lf:Rlist) (adapted_couple_opt f a b l lf) -> (adapted_couple_opt f b a l lf).
Unfold adapted_couple_opt; Unfold adapted_couple; Intros; Decompose [and] H; Clear H; Repeat Split; Try Assumption.
Rewrite H0; Unfold Rmin; Case (total_order_Rle a b); Intro; Case (total_order_Rle b a); Intro; Try Reflexivity.
Apply Rle_antisym; Assumption.
Apply Rle_antisym; Auto with real.
Rewrite H3; Unfold Rmax; Case (total_order_Rle a b); Intro; Case (total_order_Rle b a); Intro; Try Reflexivity.
Apply Rle_antisym; Assumption.
Apply Rle_antisym; Auto with real.
Qed.

Lemma StepFun_P13 : (a,b,r,r1,r3,s1,s2,r4:R;r2,lf1,s3,lf2:Rlist;f:R->R) ``a<>b`` -> (adapted_couple f a b (cons r (cons r1 r2)) (cons r3 lf1)) -> (adapted_couple_opt f a b (cons s1 (cons s2 s3)) (cons r4 lf2)) -> ``r1<=s2``.
Intros; Case (total_order_T a b); Intro.
Elim s; Intro.
EApply StepFun_P11; [Apply a0 | Apply H0 | Apply H1].
Elim H; Assumption.
EApply StepFun_P11; [Apply r0 | Apply StepFun_P2; Apply H0 | Apply StepFun_P12; Apply H1].
Qed.

Lemma StepFun_P14 : (f:R->R;l1,l2,lf1,lf2:Rlist;a,b:R) ``a<=b`` -> (adapted_couple f a b l1 lf1) -> (adapted_couple_opt f a b l2 lf2) -> (Int_SF lf1 l1)==(Int_SF lf2 l2).
Induction l1.
Intros l2 lf1 lf2 a b Hyp H H0; Unfold adapted_couple in H; Decompose [and] H; Clear H H0 H2 H3 H1 H6; Simpl in H4; Discriminate.
Induction r0.
Intros; Case (Req_EM a b); Intro.
Unfold adapted_couple_opt in H2; Elim H2; Intros; Rewrite (StepFun_P8 H4 H3); Rewrite (StepFun_P8 H1 H3); Reflexivity.
Assert H4 := (StepFun_P9 H1 H3); Simpl in H4; Elim (le_Sn_O ? (le_S_n ? ? H4)).
Intros; Clear H; Unfold adapted_couple_opt in H3; Elim H3; Clear H3; Intros; Case (Req_EM a b); Intro.
Rewrite (StepFun_P8 H2 H4); Rewrite (StepFun_P8 H H4); Reflexivity.
Assert Hyp_min : (Rmin a b)==a.
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Assert Hyp_max : (Rmax a b)==b.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Elim (RList_P20 ? (StepFun_P9 H H4)); Intros s1 [s2 [s3 H5]]; Rewrite H5 in H; Rewrite H5; Induction lf1.
Unfold adapted_couple in H2; Decompose [and] H2; Clear H H2 H4 H5 H3 H6 H8 H7 H11; Simpl in H9; Discriminate.
Clear Hreclf1; Induction lf2.
Unfold adapted_couple in H; Decompose [and] H; Clear H H2 H4 H5 H3 H6 H8 H7 H11; Simpl in H9; Discriminate.
Clear Hreclf2; Assert H6 : r==s1.
Unfold adapted_couple in H H2; Decompose [and] H; Decompose [and] H2; Clear H H2; Simpl in H13; Simpl in H8; Rewrite H13; Rewrite H8; Reflexivity.
Assert H7 : r3==r4\/r==r1.
Case (Req_EM r r1); Intro.
Right; Assumption.
Left; Cut ``r1<=s2``.
Intro; Unfold adapted_couple in H2 H; Decompose [and] H; Decompose [and] H2; Clear H H2; Pose x := ``(r+r1)/2``; Assert H18 := (H14 O); Assert H20 := (H19 O); Unfold constant_D_eq open_interval in H18 H20; Simpl in H18; Simpl in H20; Rewrite <- (H18 (lt_O_Sn ?) x).
Rewrite <- (H20 (lt_O_Sn ?) x).
Reflexivity.
Assert H21 := (H13 O (lt_O_Sn ?)); Simpl in H21; Elim H21; Intro; [Idtac | Elim H7; Assumption]; Unfold x; Split.
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Apply Rlt_compatibility; Apply H | DiscrR]].
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite <- (Rplus_sym r1); Rewrite double; Apply Rlt_compatibility; Apply H | DiscrR]].
Rewrite <- H6; Assert H21 := (H13 O (lt_O_Sn ?)); Simpl in H21; Elim H21; Intro; [Idtac | Elim H7; Assumption]; Unfold x; Split.
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Apply Rlt_compatibility; Apply H | DiscrR]].
Apply Rlt_le_trans with r1; [Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite <- (Rplus_sym r1); Rewrite double; Apply Rlt_compatibility; Apply H | DiscrR]] | Assumption].
EApply StepFun_P13.
Apply H4.
Apply H2.
Unfold adapted_couple_opt; Split.
Apply H.
Rewrite H5 in H3; Apply H3.
Assert H8 : ``r1<=s2``.
EApply StepFun_P13.
Apply H4.
Apply H2.
Unfold adapted_couple_opt; Split.
Apply H.
Rewrite H5 in H3; Apply H3.
Elim H7; Intro.
Simpl; Elim H8; Intro.
Replace ``r4*(s2-s1)`` with ``r3*(r1-r)+r3*(s2-r1)``; [Idtac | Rewrite H9; Rewrite H6; Ring].
Rewrite Rplus_assoc; Apply Rplus_plus_r; Change (Int_SF lf1 (cons r1 r2))==(Int_SF (cons r3 lf2) (cons r1 (cons s2 s3))); Apply H0 with r1 b.
Unfold adapted_couple in H2; Decompose [and] H2; Clear H2; Replace b with (Rmax a b).
Rewrite <- H12; Apply RList_P7; [Assumption | Simpl; Right; Left; Reflexivity].
EApply StepFun_P7.
Apply H1.
Apply H2.
Unfold adapted_couple_opt; Split.
Apply StepFun_P7 with a a r3.
Apply H1.
Unfold adapted_couple in H2 H; Decompose [and] H2; Decompose [and] H; Clear H H2; Assert H20 : r==a.
Simpl in H13; Rewrite H13; Apply Hyp_min.
Unfold adapted_couple; Repeat Split.
Unfold ordered_Rlist; Intros; Simpl in H; Induction i.
Simpl; Rewrite <- H20; Apply (H11 O).
Simpl; Apply lt_O_Sn.
Induction i.
Simpl; Assumption.
Change ``(pos_Rl (cons s2 s3) i)<=(pos_Rl (cons s2 s3) (S i))``; Apply (H15 (S i)); Simpl; Apply lt_S_n; Assumption.
Simpl; Symmetry; Apply Hyp_min.
Rewrite <- H17; Reflexivity.
Simpl in H19; Simpl; Rewrite H19; Reflexivity.
Intros; Simpl in H; Unfold constant_D_eq open_interval; Intros; Induction i.
Simpl; Apply (H16 O).
Simpl; Apply lt_O_Sn.
Simpl in H2; Rewrite <- H20 in H2; Unfold open_interval; Simpl; Apply H2.
Clear Hreci; Induction i.
Simpl; Simpl in H2; Rewrite H9; Apply (H21 O).
Simpl; Apply lt_O_Sn.
Unfold open_interval; Simpl; Elim H2; Intros; Split.
Apply Rle_lt_trans with r1; Try Assumption; Rewrite <- H6; Apply (H11 O); Simpl; Apply lt_O_Sn.
Assumption.
Clear Hreci; Simpl; Apply (H21 (S i)).
Simpl; Apply lt_S_n; Assumption.
Unfold open_interval; Apply H2.
Elim H3; Clear H3; Intros; Split.
Rewrite H9; Change (i:nat) (lt i (pred (Rlength (cons r4 lf2)))) ->``(pos_Rl (cons r4 lf2) i)<>(pos_Rl (cons r4 lf2) (S i))``\/``(f (pos_Rl (cons s1 (cons s2 s3)) (S i)))<>(pos_Rl (cons r4 lf2) i)``; Rewrite <- H5; Apply H3.
Rewrite H5 in H11; Intros; Simpl in H12; Induction i.
Simpl; Red; Intro; Rewrite H13 in H10; Elim (Rlt_antirefl ? H10).
Clear Hreci; Apply (H11 (S i)); Simpl; Apply H12.
Rewrite H9; Rewrite H10; Rewrite H6; Apply Rplus_plus_r; Rewrite <- H10; Apply H0 with r1 b.
Unfold adapted_couple in H2; Decompose [and] H2; Clear H2; Replace b with (Rmax a b).
Rewrite <- H12; Apply RList_P7; [Assumption | Simpl; Right; Left; Reflexivity].
EApply StepFun_P7.
Apply H1.
Apply H2.
Unfold adapted_couple_opt; Split.
Apply StepFun_P7 with a a r3.
Apply H1.
Unfold adapted_couple in H2 H; Decompose [and] H2; Decompose [and] H; Clear H H2; Assert H20 : r==a.
Simpl in H13; Rewrite H13; Apply Hyp_min.
Unfold adapted_couple; Repeat Split.
Unfold ordered_Rlist; Intros; Simpl in H; Induction i.
Simpl; Rewrite <- H20; Apply (H11 O); Simpl; Apply lt_O_Sn.
Rewrite H10; Apply (H15 (S i)); Simpl; Assumption.
Simpl; Symmetry; Apply Hyp_min.
Rewrite <- H17; Rewrite H10; Reflexivity.
Simpl in H19; Simpl; Apply H19.
Intros; Simpl in H; Unfold constant_D_eq open_interval; Intros; Induction i.
Simpl; Apply (H16 O).
Simpl; Apply lt_O_Sn.
Simpl in H2; Rewrite <- H20 in H2; Unfold open_interval; Simpl; Apply H2.
Clear Hreci; Simpl; Apply (H21 (S i)).
Simpl; Assumption.
Rewrite <- H10; Unfold open_interval; Apply H2.
Elim H3; Clear H3; Intros; Split.
Rewrite H5 in H3; Intros; Apply (H3 (S i)).
Simpl; Replace (Rlength lf2) with (S (pred (Rlength lf2))).
Apply lt_n_S; Apply H12.
Symmetry; Apply S_pred with O; Apply neq_O_lt; Red; Intro; Rewrite <- H13 in H12; Elim (lt_n_O ? H12).
Intros; Simpl in H12; Rewrite H10; Rewrite H5 in H11; Apply (H11 (S i)); Simpl; Apply lt_n_S; Apply H12.
Simpl; Rewrite H9; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rmult_Or; Rewrite Rplus_Ol; Change (Int_SF lf1 (cons r1 r2))==(Int_SF (cons r4 lf2) (cons s1 (cons s2 s3))); EApply H0.
Apply H1.
2: Rewrite H5 in H3; Unfold adapted_couple_opt; Split; Assumption.
Assert H10 : r==a.
Unfold adapted_couple in H2; Decompose [and] H2; Clear H2; Simpl in H12; Rewrite H12; Apply Hyp_min.
Rewrite <- H9; Rewrite H10; Apply StepFun_P7 with a r r3; [Apply H1 | Pattern 2 a; Rewrite <- H10; Pattern 2 r; Rewrite H9; Apply H2].
Qed.

Lemma StepFun_P15 : (f:R->R;l1,l2,lf1,lf2:Rlist;a,b:R) (adapted_couple f a b l1 lf1) -> (adapted_couple_opt f a b l2 lf2) -> (Int_SF lf1 l1)==(Int_SF lf2 l2).
Intros; Case (total_order_Rle a b); Intro; [Apply (StepFun_P14 r H H0) | Assert H1 : ``b<=a``; [Auto with real | EApply StepFun_P14; [Apply H1 | Apply StepFun_P2; Apply H | Apply StepFun_P12; Apply H0]]].
Qed.

Lemma StepFun_P16 : (f:R->R;l,lf:Rlist;a,b:R) (adapted_couple f a b l lf) -> (EXT l':Rlist | (EXT lf':Rlist | (adapted_couple_opt f a b l' lf'))). 
Intros; Case (total_order_Rle a b); Intro; [Apply (StepFun_P10 r H) | Assert H1 : ``b<=a``; [Auto with real | Assert H2 := (StepFun_P10 H1 (StepFun_P2 H)); Elim H2; Intros l' [lf' H3]; Exists l'; Exists lf'; Apply StepFun_P12; Assumption]].
Qed.

Lemma StepFun_P17 : (f:R->R;l1,l2,lf1,lf2:Rlist;a,b:R) (adapted_couple f a b l1 lf1) -> (adapted_couple f a b l2 lf2) -> (Int_SF lf1 l1)==(Int_SF lf2 l2).
Intros; Elim (StepFun_P16 H); Intros l' [lf' H1]; Rewrite (StepFun_P15 H H1); Rewrite (StepFun_P15 H0 H1); Reflexivity.
Qed.

Lemma StepFun_P18 : (a,b,c:R) (RiemannInt_SF (mkStepFun (StepFun_P4 a b c)))==``c*(b-a)``.
Intros; Unfold RiemannInt_SF; Case (total_order_Rle a b); Intro.
Replace (Int_SF (subdivision_val (mkStepFun (StepFun_P4 a b c))) (subdivision (mkStepFun (StepFun_P4 a b c)))) with (Int_SF (cons c nil) (cons a (cons b nil))); [Simpl; Ring | Apply StepFun_P17 with (fct_cte c) a b; [Apply StepFun_P3; Assumption | Apply (StepFun_P1 (mkStepFun (StepFun_P4 a b c)))]].
Replace (Int_SF (subdivision_val (mkStepFun (StepFun_P4 a b c))) (subdivision (mkStepFun (StepFun_P4 a b c)))) with (Int_SF (cons c nil) (cons b (cons a nil))); [Simpl; Ring | Apply StepFun_P17 with (fct_cte c) a b; [Apply StepFun_P2; Apply StepFun_P3; Auto with real | Apply (StepFun_P1 (mkStepFun (StepFun_P4 a b c)))]].
Qed.

Lemma StepFun_P19 : (l1:Rlist;f,g:R->R;l:R) (Int_SF (FF l1 [x:R]``(f x)+l*(g x)``) l1)==``(Int_SF (FF l1 f) l1)+l*(Int_SF (FF l1 g) l1)``.
Intros; Induction l1; [Simpl; Ring | Induction l1; Simpl; [Ring | Simpl in Hrecl1; Rewrite Hrecl1; Ring]].
Qed.

Lemma StepFun_P20 : (l:Rlist;f:R->R) (lt O (Rlength l)) -> (Rlength l)=(S (Rlength (FF l f))).
Intros l f H; NewInduction l; [Elim (lt_n_n ? H) | Simpl; Rewrite RList_P18; Rewrite RList_P14; Reflexivity].
Qed.

Lemma StepFun_P21 : (a,b:R;f:R->R;l:Rlist) (is_subdivision f a b l) -> (adapted_couple f a b l (FF l f)).
Intros; Unfold adapted_couple; Unfold is_subdivision in X; Unfold adapted_couple in X; Elim X; Clear X; Intros; Decompose [and] p; Clear p; Repeat Split; Try Assumption.
Apply StepFun_P20; Rewrite H2; Apply lt_O_Sn.
Intros; Assert H5 := (H4 ? H3); Unfold constant_D_eq open_interval in H5; Unfold constant_D_eq open_interval; Intros; Induction l.
Discriminate.
Unfold FF; Rewrite RList_P12.
Simpl; Change (f x0)==(f (pos_Rl (mid_Rlist (cons r l) r) (S i))); Rewrite RList_P13; Try Assumption; Rewrite (H5 x0 H6); Rewrite H5.
Reflexivity.
Split.
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Apply Rlt_compatibility; Elim H6; Intros; Apply Rlt_trans with x0; Assumption | DiscrR]].
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Rewrite (Rplus_sym (pos_Rl (cons r l) i)); Apply Rlt_compatibility; Elim H6; Intros; Apply Rlt_trans with x0; Assumption | DiscrR]].
Rewrite RList_P14; Simpl in H3; Apply H3.
Qed.

Lemma StepFun_P22 : (a,b:R;f,g:R->R;lf,lg:Rlist) ``a<=b`` -> (is_subdivision f a b lf) -> (is_subdivision g a b lg) -> (is_subdivision f a b (cons_ORlist lf lg)).
Unfold is_subdivision; Intros a b f g lf lg Hyp X X0; Elim X; Elim X0; Clear X X0; Intros lg0 p lf0 p0; Assert Hyp_min : (Rmin a b)==a.
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Assert Hyp_max : (Rmax a b)==b.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Apply existTT with (FF (cons_ORlist lf lg) f); Unfold adapted_couple in p p0; Decompose [and] p; Decompose [and] p0; Clear p p0; Rewrite Hyp_min in H6; Rewrite Hyp_min in H1; Rewrite Hyp_max in H0; Rewrite Hyp_max in H5; Unfold adapted_couple; Repeat Split.
Apply RList_P2; Assumption.
Rewrite Hyp_min; Symmetry; Apply Rle_antisym.
Induction lf.
Simpl; Right; Symmetry; Assumption.
Assert H10 : (In (pos_Rl (cons_ORlist (cons r lf) lg) (0)) (cons_ORlist (cons r lf) lg)).
Elim (RList_P3 (cons_ORlist (cons r lf) lg) (pos_Rl (cons_ORlist (cons r lf) lg) (0))); Intros _ H10; Apply H10; Exists O; Split; [Reflexivity | Rewrite RList_P11; Simpl; Apply lt_O_Sn].
Elim (RList_P9 (cons r lf) lg (pos_Rl (cons_ORlist (cons r lf) lg) (0))); Intros H12 _; Assert H13 := (H12 H10); Elim H13; Intro.
Elim (RList_P3 (cons r lf) (pos_Rl (cons_ORlist (cons r lf) lg) (0))); Intros H11 _; Assert H14 := (H11 H8); Elim H14; Intros; Elim H15; Clear H15; Intros; Rewrite H15; Rewrite <- H6; Elim (RList_P6 (cons r lf)); Intros; Apply H17; [Assumption | Apply le_O_n | Assumption].
Elim (RList_P3 lg (pos_Rl (cons_ORlist (cons r lf) lg) (0))); Intros H11 _; Assert H14 := (H11 H8); Elim H14; Intros; Elim H15; Clear H15; Intros; Rewrite H15; Rewrite <- H1; Elim (RList_P6 lg); Intros; Apply H17; [Assumption | Apply le_O_n | Assumption].
Induction lf.
Simpl; Right; Assumption.
Assert H8 : (In a (cons_ORlist (cons r lf) lg)).
Elim (RList_P9 (cons r lf) lg a); Intros; Apply H10; Left; Elim (RList_P3 (cons r lf) a); Intros; Apply H12; Exists O; Split; [Symmetry; Assumption | Simpl; Apply lt_O_Sn].
Apply RList_P5; [Apply RList_P2; Assumption | Assumption].
Rewrite Hyp_max; Apply Rle_antisym.
Induction lf.
Simpl; Right; Assumption.
Assert H8 : (In (pos_Rl (cons_ORlist (cons r lf) lg) (pred (Rlength (cons_ORlist (cons r lf) lg)))) (cons_ORlist (cons r lf) lg)).
Elim (RList_P3 (cons_ORlist (cons r lf) lg) (pos_Rl (cons_ORlist (cons r lf) lg) (pred (Rlength (cons_ORlist (cons r lf) lg))))); Intros _ H10; Apply H10; Exists (pred (Rlength (cons_ORlist (cons r lf) lg))); Split; [Reflexivity | Rewrite RList_P11; Simpl; Apply lt_n_Sn].
Elim (RList_P9 (cons r lf) lg (pos_Rl (cons_ORlist (cons r lf) lg) (pred (Rlength (cons_ORlist (cons r lf) lg))))); Intros H10 _.
Assert H11 := (H10 H8); Elim H11; Intro.
Elim (RList_P3 (cons r lf) (pos_Rl (cons_ORlist (cons r lf) lg) (pred (Rlength (cons_ORlist (cons r lf) lg))))); Intros H13 _; Assert H14 := (H13 H12); Elim H14; Intros; Elim H15; Clear H15; Intros; Rewrite H15; Rewrite <- H5; Elim (RList_P6 (cons r lf)); Intros; Apply H17; [Assumption | Simpl; Simpl in H14; Apply lt_n_Sm_le; Assumption | Simpl; Apply lt_n_Sn].
Elim (RList_P3 lg (pos_Rl (cons_ORlist (cons r lf) lg) (pred (Rlength (cons_ORlist (cons r lf) lg))))); Intros H13 _; Assert H14 := (H13 H12); Elim H14; Intros; Elim H15; Clear H15; Intros.
Rewrite H15; Assert H17 : (Rlength lg)=(S (pred (Rlength lg))).
Apply S_pred with O; Apply neq_O_lt; Red; Intro; Rewrite <- H17 in H16; Elim (lt_n_O ? H16).
Rewrite <- H0; Elim (RList_P6 lg); Intros; Apply H18; [Assumption | Rewrite H17 in H16; Apply lt_n_Sm_le; Assumption | Apply lt_pred_n_n; Rewrite H17; Apply lt_O_Sn].
Induction lf.
Simpl; Right; Symmetry; Assumption.
Assert H8 : (In b (cons_ORlist (cons r lf) lg)).
Elim (RList_P9 (cons r lf) lg b); Intros; Apply H10; Left; Elim (RList_P3 (cons r lf) b); Intros; Apply H12; Exists (pred (Rlength (cons r lf))); Split; [Symmetry; Assumption | Simpl; Apply lt_n_Sn].
Apply RList_P7; [Apply RList_P2; Assumption | Assumption].
Apply StepFun_P20; Rewrite RList_P11; Rewrite H2; Rewrite H7; Simpl; Apply lt_O_Sn.
Intros; Unfold constant_D_eq open_interval; Intros; Cut (EXT l:R | (constant_D_eq f (open_interval (pos_Rl (cons_ORlist lf lg) i) (pos_Rl (cons_ORlist lf lg) (S i))) l)).
Intros; Elim H11; Clear H11; Intros; Assert H12 := H11; Assert Hyp_cons : (EXT r:R | (EXT r0:Rlist | (cons_ORlist lf lg)==(cons r r0))).
Apply RList_P19; Red; Intro; Rewrite H13 in H8; Elim (lt_n_O ? H8).
Elim Hyp_cons; Clear Hyp_cons; Intros r [r0 Hyp_cons]; Rewrite Hyp_cons; Unfold FF; Rewrite RList_P12.
Change (f x)==(f (pos_Rl (mid_Rlist (cons r r0) r) (S i))); Rewrite <- Hyp_cons; Rewrite RList_P13.
Assert H13 := (RList_P2 ? ? H ? H8); Elim H13; Intro.
Unfold constant_D_eq open_interval in H11 H12; Rewrite (H11 x H10); Assert H15 : ``(pos_Rl (cons_ORlist lf lg) i)<((pos_Rl (cons_ORlist lf lg) i)+(pos_Rl (cons_ORlist lf lg) (S i)))/2<(pos_Rl (cons_ORlist lf lg) (S i))``.
Split.
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Apply Rlt_compatibility; Assumption | DiscrR]].
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Rewrite (Rplus_sym (pos_Rl (cons_ORlist lf lg) i)); Apply Rlt_compatibility; Assumption | DiscrR]].
Rewrite (H11 ? H15); Reflexivity.
Elim H10; Intros; Rewrite H14 in H15; Elim (Rlt_antirefl ? (Rlt_trans ? ? ? H16 H15)).
Apply H8.
Rewrite RList_P14; Rewrite Hyp_cons in H8; Simpl in H8; Apply H8.
Assert H11 : ``a<b``.
Apply Rle_lt_trans with (pos_Rl (cons_ORlist lf lg) i).
Rewrite <- H6; Rewrite <- (RList_P15 lf lg).
Elim (RList_P6 (cons_ORlist lf lg)); Intros; Apply H11.
Apply RList_P2; Assumption.
Apply le_O_n.
Apply lt_trans with (pred (Rlength (cons_ORlist lf lg))); [Assumption | Apply lt_pred_n_n; Apply neq_O_lt; Red; Intro; Rewrite <- H13 in H8; Elim (lt_n_O ? H8)].
Assumption.
Assumption.
Rewrite H1; Assumption.
Apply Rlt_le_trans with (pos_Rl (cons_ORlist lf lg) (S i)).
Elim H10; Intros; Apply Rlt_trans with x; Assumption.
Rewrite <- H5; Rewrite <- (RList_P16 lf lg); Try Assumption.
Elim (RList_P6 (cons_ORlist lf lg)); Intros; Apply H11.
Apply RList_P2; Assumption.
Apply lt_n_Sm_le; Apply lt_n_S; Assumption.
Apply lt_pred_n_n; Apply neq_O_lt; Red; Intro; Rewrite <- H13 in H8; Elim (lt_n_O ? H8).
Rewrite H0; Assumption.
Pose I := [j:nat]``(pos_Rl lf j)<=(pos_Rl (cons_ORlist lf lg) i)``/\(lt j (Rlength lf)); Assert H12 : (Nbound I).
Unfold Nbound; Exists (Rlength lf); Intros; Unfold I in H12; Elim H12; Intros; Apply lt_le_weak; Assumption.
Assert H13 : (EX n:nat | (I n)).
Exists O; Unfold I; Split.
Apply Rle_trans with (pos_Rl (cons_ORlist lf lg) O).
Right; Symmetry.
Apply RList_P15; Try Assumption; Rewrite H1; Assumption.
Elim (RList_P6 (cons_ORlist lf lg)); Intros; Apply H13.
Apply RList_P2; Assumption.
Apply le_O_n.
Apply lt_trans with (pred (Rlength (cons_ORlist lf lg))).
Assumption.
Apply lt_pred_n_n; Apply neq_O_lt; Red; Intro; Rewrite <- H15 in H8; Elim (lt_n_O ? H8).
Apply neq_O_lt; Red; Intro; Rewrite <- H13 in H5; Rewrite <- H6 in H11; Rewrite <- H5 in H11; Elim (Rlt_antirefl ? H11).
Assert H14 := (Nzorn H13 H12); Elim H14; Clear H14; Intros x0 H14; Exists (pos_Rl lf0 x0); Unfold constant_D_eq open_interval; Intros; Assert H16 := (H9 x0); Assert H17 : (lt x0 (pred (Rlength lf))).
Elim H14; Clear H14; Intros; Unfold I in H14; Elim H14; Clear H14; Intros; Apply lt_S_n; Replace (S (pred (Rlength lf))) with (Rlength lf).
Inversion H18.
2:Apply lt_n_S; Assumption.
Cut x0=(pred (Rlength lf)).
Intro; Rewrite H19 in H14; Rewrite H5 in H14; Cut ``(pos_Rl (cons_ORlist lf lg) i)<b``.
Intro; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H14 H21)).
Apply Rlt_le_trans with (pos_Rl (cons_ORlist lf lg) (S i)).
Elim H10; Intros; Apply Rlt_trans with x; Assumption.
Rewrite <- H5; Apply Rle_trans with (pos_Rl (cons_ORlist lf lg) (pred (Rlength (cons_ORlist lf lg)))).
Elim (RList_P6 (cons_ORlist lf lg)); Intros; Apply H21.
Apply RList_P2; Assumption.
Apply lt_n_Sm_le; Apply lt_n_S; Assumption.
Apply lt_pred_n_n; Apply neq_O_lt; Red; Intro; Rewrite <- H23 in H8; Elim (lt_n_O ? H8).
Right; Apply RList_P16; Try Assumption; Rewrite H0; Assumption.
Rewrite <- H20; Reflexivity.
Apply S_pred with O; Apply neq_O_lt; Red; Intro; Rewrite <- H19 in H18; Elim (lt_n_O ? H18).
Assert H18 := (H16 H17); Unfold constant_D_eq open_interval in H18; Rewrite (H18 x1).
Reflexivity.
Elim H15; Clear H15; Intros; Elim H14; Clear H14; Intros; Unfold I in H14; Elim H14; Clear H14; Intros; Split.
Apply Rle_lt_trans with (pos_Rl (cons_ORlist lf lg) i); Assumption.
Apply Rlt_le_trans with (pos_Rl (cons_ORlist lf lg) (S i)); Try Assumption.
Assert H22 : (lt (S x0) (Rlength lf)).
Replace (Rlength lf) with (S (pred (Rlength lf))); [Apply lt_n_S; Assumption | Symmetry; Apply S_pred with O; Apply neq_O_lt; Red; Intro; Rewrite <- H22 in H21; Elim (lt_n_O ? H21)].
Elim (total_order_Rle (pos_Rl lf (S x0)) (pos_Rl (cons_ORlist lf lg) i)); Intro.
Assert H23 : (le (S x0) x0).
Apply H20; Unfold I; Split; Assumption.
Elim (le_Sn_n ? H23).
Assert H23 : ``(pos_Rl (cons_ORlist lf lg) i)<(pos_Rl lf (S x0))``.
Auto with real.
Clear b0; Apply RList_P17; Try Assumption.
Apply RList_P2; Assumption.
Elim (RList_P9 lf lg (pos_Rl lf (S x0))); Intros; Apply H25; Left; Elim (RList_P3 lf (pos_Rl lf (S x0))); Intros; Apply H27; Exists (S x0); Split; [Reflexivity | Apply H22].
Qed.

Lemma StepFun_P23 : (a,b:R;f,g:R->R;lf,lg:Rlist) (is_subdivision f a b lf) -> (is_subdivision g a b lg) -> (is_subdivision f a b (cons_ORlist lf lg)).
Intros; Case (total_order_Rle a b); Intro; [Apply StepFun_P22 with g; Assumption | Apply StepFun_P5; Apply StepFun_P22 with g; [Auto with real | Apply StepFun_P5; Assumption | Apply StepFun_P5; Assumption]].
Qed.

Lemma StepFun_P24 : (a,b:R;f,g:R->R;lf,lg:Rlist) ``a<=b`` -> (is_subdivision f a b lf) -> (is_subdivision g a b lg) -> (is_subdivision g a b (cons_ORlist lf lg)).
Unfold is_subdivision; Intros a b f g lf lg Hyp X X0; Elim X; Elim X0; Clear X X0; Intros lg0 p lf0 p0; Assert Hyp_min : (Rmin a b)==a.
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Assert Hyp_max : (Rmax a b)==b.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Apply existTT with (FF (cons_ORlist lf lg) g); Unfold adapted_couple in p p0; Decompose [and] p; Decompose [and] p0; Clear p p0; Rewrite Hyp_min in H1; Rewrite Hyp_min in H6; Rewrite Hyp_max in H0; Rewrite Hyp_max in H5; Unfold adapted_couple; Repeat Split.
Apply RList_P2; Assumption.
Rewrite Hyp_min; Symmetry; Apply Rle_antisym.
Induction lf.
Simpl; Right; Symmetry; Assumption.
Assert H10 : (In (pos_Rl (cons_ORlist (cons r lf) lg) (0)) (cons_ORlist (cons r lf) lg)).
Elim (RList_P3 (cons_ORlist (cons r lf) lg) (pos_Rl (cons_ORlist (cons r lf) lg) (0))); Intros _ H10; Apply H10; Exists O; Split; [Reflexivity | Rewrite RList_P11; Simpl; Apply lt_O_Sn].
Elim (RList_P9 (cons r lf) lg (pos_Rl (cons_ORlist (cons r lf) lg) (0))); Intros H12 _; Assert H13 := (H12 H10); Elim H13; Intro.
Elim (RList_P3 (cons r lf) (pos_Rl (cons_ORlist (cons r lf) lg) (0))); Intros H11 _; Assert H14 := (H11 H8); Elim H14; Intros; Elim H15; Clear H15; Intros; Rewrite H15; Rewrite <- H6; Elim (RList_P6 (cons r lf)); Intros; Apply H17; [Assumption | Apply le_O_n | Assumption].
Elim (RList_P3 lg (pos_Rl (cons_ORlist (cons r lf) lg) (0))); Intros H11 _; Assert H14 := (H11 H8); Elim H14; Intros; Elim H15; Clear H15; Intros; Rewrite H15; Rewrite <- H1; Elim (RList_P6 lg); Intros; Apply H17; [Assumption | Apply le_O_n | Assumption].
Induction lf.
Simpl; Right; Assumption.
Assert H8 : (In a (cons_ORlist (cons r lf) lg)).
Elim (RList_P9 (cons r lf) lg a); Intros; Apply H10; Left; Elim (RList_P3 (cons r lf) a); Intros; Apply H12; Exists O; Split; [Symmetry; Assumption | Simpl; Apply lt_O_Sn].
Apply RList_P5; [Apply RList_P2; Assumption | Assumption].
Rewrite Hyp_max; Apply Rle_antisym.
Induction lf.
Simpl; Right; Assumption.
Assert H8 : (In (pos_Rl (cons_ORlist (cons r lf) lg) (pred (Rlength (cons_ORlist (cons r lf) lg)))) (cons_ORlist (cons r lf) lg)).
Elim (RList_P3 (cons_ORlist (cons r lf) lg) (pos_Rl (cons_ORlist (cons r lf) lg) (pred (Rlength (cons_ORlist (cons r lf) lg))))); Intros _ H10; Apply H10; Exists (pred (Rlength (cons_ORlist (cons r lf) lg))); Split; [Reflexivity | Rewrite RList_P11; Simpl; Apply lt_n_Sn].
Elim (RList_P9 (cons r lf) lg (pos_Rl (cons_ORlist (cons r lf) lg) (pred (Rlength (cons_ORlist (cons r lf) lg))))); Intros H10 _; Assert H11 := (H10 H8); Elim H11; Intro.
Elim (RList_P3 (cons r lf) (pos_Rl (cons_ORlist (cons r lf) lg) (pred (Rlength (cons_ORlist (cons r lf) lg))))); Intros H13 _; Assert H14 := (H13 H12); Elim H14; Intros; Elim H15; Clear H15; Intros; Rewrite H15; Rewrite <- H5; Elim (RList_P6 (cons r lf)); Intros; Apply H17; [Assumption | Simpl; Simpl in H14; Apply lt_n_Sm_le; Assumption | Simpl; Apply lt_n_Sn].
Elim (RList_P3 lg (pos_Rl (cons_ORlist (cons r lf) lg) (pred (Rlength (cons_ORlist (cons r lf) lg))))); Intros H13 _; Assert H14 := (H13 H12); Elim H14; Intros; Elim H15; Clear H15; Intros; Rewrite H15; Assert H17 : (Rlength lg)=(S (pred (Rlength lg))).
Apply S_pred with O; Apply neq_O_lt; Red; Intro; Rewrite <- H17 in H16; Elim (lt_n_O ? H16).
Rewrite <- H0; Elim (RList_P6 lg); Intros; Apply H18; [Assumption | Rewrite H17 in H16; Apply lt_n_Sm_le; Assumption | Apply lt_pred_n_n; Rewrite H17; Apply lt_O_Sn].
Induction lf.
Simpl; Right; Symmetry; Assumption.
Assert H8 : (In b (cons_ORlist (cons r lf) lg)).
Elim (RList_P9 (cons r lf) lg b); Intros; Apply H10; Left; Elim (RList_P3 (cons r lf) b); Intros; Apply H12; Exists (pred (Rlength (cons r lf))); Split; [Symmetry; Assumption | Simpl; Apply lt_n_Sn].
Apply RList_P7; [Apply RList_P2; Assumption | Assumption].
Apply StepFun_P20; Rewrite RList_P11; Rewrite H7; Rewrite H2; Simpl; Apply lt_O_Sn.
Unfold constant_D_eq open_interval; Intros; Cut (EXT l:R | (constant_D_eq g (open_interval (pos_Rl (cons_ORlist lf lg) i) (pos_Rl (cons_ORlist lf lg) (S i))) l)).
Intros; Elim H11; Clear H11; Intros;  Assert H12 := H11; Assert Hyp_cons : (EXT r:R | (EXT r0:Rlist | (cons_ORlist lf lg)==(cons r r0))).
Apply RList_P19; Red; Intro; Rewrite H13 in H8; Elim (lt_n_O ? H8).
Elim Hyp_cons; Clear Hyp_cons; Intros r [r0 Hyp_cons]; Rewrite Hyp_cons; Unfold FF; Rewrite RList_P12.
Change (g x)==(g (pos_Rl (mid_Rlist (cons r r0) r) (S i))); Rewrite <- Hyp_cons; Rewrite RList_P13.
Assert H13 := (RList_P2 ? ? H ? H8); Elim H13; Intro.
Unfold constant_D_eq open_interval in H11 H12; Rewrite (H11 x H10); Assert H15 : ``(pos_Rl (cons_ORlist lf lg) i)<((pos_Rl (cons_ORlist lf lg) i)+(pos_Rl (cons_ORlist lf lg) (S i)))/2<(pos_Rl (cons_ORlist lf lg) (S i))``.
Split.
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Apply Rlt_compatibility; Assumption | DiscrR]].
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Rewrite (Rplus_sym (pos_Rl (cons_ORlist lf lg) i)); Apply Rlt_compatibility; Assumption | DiscrR]].
Rewrite (H11 ? H15); Reflexivity.
Elim H10; Intros; Rewrite H14 in H15; Elim (Rlt_antirefl ? (Rlt_trans ? ? ? H16 H15)).
Apply H8.
Rewrite RList_P14; Rewrite Hyp_cons in H8; Simpl in H8; Apply H8.
Assert H11 : ``a<b``.
Apply Rle_lt_trans with (pos_Rl (cons_ORlist lf lg) i).
Rewrite <- H6; Rewrite <- (RList_P15 lf lg); Try Assumption.
Elim (RList_P6 (cons_ORlist lf lg)); Intros; Apply H11.
Apply RList_P2; Assumption.
Apply le_O_n.
Apply lt_trans with (pred (Rlength (cons_ORlist lf lg))); [Assumption | Apply lt_pred_n_n; Apply neq_O_lt; Red; Intro; Rewrite <- H13 in H8; Elim (lt_n_O ? H8)].
Rewrite H1; Assumption.
Apply Rlt_le_trans with (pos_Rl (cons_ORlist lf lg) (S i)).
Elim H10; Intros; Apply Rlt_trans with x; Assumption.
Rewrite <- H5; Rewrite <- (RList_P16 lf lg); Try Assumption.
Elim (RList_P6 (cons_ORlist lf lg)); Intros; Apply H11.
Apply RList_P2; Assumption.
Apply lt_n_Sm_le; Apply lt_n_S; Assumption.
Apply lt_pred_n_n; Apply neq_O_lt; Red; Intro; Rewrite <- H13 in H8; Elim (lt_n_O ? H8).
Rewrite H0; Assumption.
Pose I := [j:nat]``(pos_Rl lg j)<=(pos_Rl (cons_ORlist lf lg) i)``/\(lt j (Rlength lg)); Assert H12 : (Nbound I).
Unfold Nbound; Exists (Rlength lg); Intros; Unfold I in H12; Elim H12; Intros; Apply lt_le_weak; Assumption.
Assert H13 : (EX n:nat | (I n)).
Exists O; Unfold I; Split.
Apply Rle_trans with (pos_Rl (cons_ORlist lf lg) O).
Right; Symmetry; Rewrite H1; Rewrite <- H6; Apply RList_P15; Try Assumption; Rewrite H1; Assumption.
Elim (RList_P6 (cons_ORlist lf lg)); Intros; Apply H13; [Apply RList_P2; Assumption | Apply le_O_n | Apply lt_trans with (pred (Rlength (cons_ORlist lf lg))); [Assumption | Apply lt_pred_n_n; Apply neq_O_lt; Red; Intro; Rewrite <- H15 in H8; Elim (lt_n_O ? H8)]].
Apply neq_O_lt; Red; Intro; Rewrite <- H13 in H0; Rewrite <- H1 in H11; Rewrite <- H0 in H11; Elim (Rlt_antirefl ? H11).
Assert H14 := (Nzorn H13 H12); Elim H14; Clear H14; Intros x0 H14; Exists (pos_Rl lg0 x0); Unfold constant_D_eq open_interval; Intros; Assert H16 := (H4 x0); Assert H17 : (lt x0 (pred (Rlength lg))).
Elim H14; Clear H14; Intros; Unfold I in H14; Elim H14; Clear H14; Intros; Apply lt_S_n; Replace (S (pred (Rlength lg))) with (Rlength lg).
Inversion H18.
2:Apply lt_n_S; Assumption.
Cut x0=(pred (Rlength lg)).
Intro; Rewrite H19 in H14; Rewrite H0 in H14; Cut ``(pos_Rl (cons_ORlist lf lg) i)<b``.
Intro; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H14 H21)).
Apply Rlt_le_trans with (pos_Rl (cons_ORlist lf lg) (S i)).
Elim H10; Intros; Apply Rlt_trans with x; Assumption.
Rewrite <- H0; Apply Rle_trans with (pos_Rl (cons_ORlist lf lg) (pred (Rlength (cons_ORlist lf lg)))).
Elim (RList_P6 (cons_ORlist lf lg)); Intros; Apply H21.
Apply RList_P2; Assumption.
Apply lt_n_Sm_le; Apply lt_n_S; Assumption.
Apply lt_pred_n_n; Apply neq_O_lt; Red; Intro; Rewrite <- H23 in H8; Elim (lt_n_O ? H8).
Right; Rewrite H0; Rewrite <- H5; Apply RList_P16; Try Assumption.
Rewrite H0; Assumption.
Rewrite <- H20; Reflexivity.
Apply S_pred with O; Apply neq_O_lt; Red; Intro; Rewrite <- H19 in H18; Elim (lt_n_O ? H18).
Assert H18 := (H16 H17); Unfold constant_D_eq open_interval in H18; Rewrite (H18 x1).
Reflexivity.
Elim H15; Clear H15; Intros; Elim H14; Clear H14; Intros; Unfold I in H14; Elim H14; Clear H14; Intros; Split.
Apply Rle_lt_trans with (pos_Rl (cons_ORlist lf lg) i); Assumption.
Apply Rlt_le_trans with (pos_Rl (cons_ORlist lf lg) (S i)); Try Assumption.
Assert H22 : (lt (S x0) (Rlength lg)).
Replace (Rlength lg) with (S (pred (Rlength lg))).
Apply lt_n_S; Assumption.
Symmetry; Apply S_pred with O; Apply neq_O_lt; Red; Intro; Rewrite <- H22 in H21; Elim (lt_n_O ? H21).
Elim (total_order_Rle (pos_Rl lg (S x0)) (pos_Rl (cons_ORlist lf lg) i)); Intro.
Assert H23 : (le (S x0) x0); [Apply H20; Unfold I; Split; Assumption | Elim (le_Sn_n ? H23)].
Assert H23 : ``(pos_Rl (cons_ORlist lf lg) i)<(pos_Rl lg (S x0))``.
Auto with real.
Clear b0; Apply RList_P17; Try Assumption; [Apply RList_P2; Assumption | Elim (RList_P9 lf lg (pos_Rl lg (S x0))); Intros; Apply H25; Right; Elim (RList_P3 lg (pos_Rl lg (S x0))); Intros; Apply H27; Exists (S x0); Split; [Reflexivity | Apply H22]].
Qed.

Lemma StepFun_P25 : (a,b:R;f,g:R->R;lf,lg:Rlist) (is_subdivision f a b lf) -> (is_subdivision g a b lg) -> (is_subdivision g a b (cons_ORlist lf lg)).
Intros a b f g lf lg H H0; Case (total_order_Rle a b); Intro; [Apply StepFun_P24 with f; Assumption | Apply StepFun_P5; Apply StepFun_P24 with f; [Auto with real | Apply StepFun_P5; Assumption | Apply StepFun_P5; Assumption]].
Qed.

Lemma StepFun_P26 : (a,b,l:R;f,g:R->R;l1:Rlist) (is_subdivision f a b l1) -> (is_subdivision g a b l1) -> (is_subdivision [x:R]``(f x)+l*(g x)`` a b l1).
Intros a b l f g l1; Unfold is_subdivision; Intros; Elim X; Elim X0; Intros; Clear X X0; Unfold adapted_couple in p p0; Decompose [and] p; Decompose [and] p0; Clear p p0; Apply existTT with (FF l1 [x:R]``(f x)+l*(g x)``); Unfold adapted_couple; Repeat Split; Try Assumption.
Apply StepFun_P20; Apply neq_O_lt; Red; Intro; Rewrite <- H8 in H7; Discriminate.
Intros; Unfold constant_D_eq open_interval; Unfold constant_D_eq open_interval in H9 H4; Intros; Rewrite (H9 ? H8 ? H10); Rewrite (H4 ? H8 ? H10); Assert H11 : ~l1==nil.
Red; Intro; Rewrite H11 in H8; Elim (lt_n_O ? H8).
Assert H12 := (RList_P19 ? H11); Elim H12; Clear H12; Intros r [r0 H12]; Rewrite H12; Unfold FF; Change ``(pos_Rl x0 i)+l*(pos_Rl x i)`` == (pos_Rl (app_Rlist (mid_Rlist (cons r r0) r) [x2:R]``(f x2)+l*(g x2)``) (S i)); Rewrite RList_P12.
Rewrite RList_P13.
Rewrite <- H12; Rewrite (H9 ? H8); Try Rewrite (H4 ? H8); Reflexivity Orelse (Elim H10; Clear H10; Intros; Split; [Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Apply Rlt_compatibility; Apply Rlt_trans with x1; Assumption | DiscrR]] | Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Rewrite (Rplus_sym (pos_Rl l1 i)); Apply Rlt_compatibility; Apply Rlt_trans with x1; Assumption | DiscrR]]]).
Rewrite <- H12; Assumption.
Rewrite RList_P14; Simpl; Rewrite H12 in H8; Simpl in H8; Apply lt_n_S; Apply H8.
Qed.

Lemma StepFun_P27 : (a,b,l:R;f,g:R->R;lf,lg:Rlist) (is_subdivision f a b lf) -> (is_subdivision g a b lg) -> (is_subdivision [x:R]``(f x)+l*(g x)`` a b (cons_ORlist lf lg)).
Intros a b l f g lf lg H H0; Apply StepFun_P26; [Apply StepFun_P23 with g; Assumption | Apply StepFun_P25 with f; Assumption].
Qed.

(* The set of step functions on [a,b] is a vectorial space *)
Lemma StepFun_P28 : (a,b,l:R;f,g:(StepFun a b)) (IsStepFun [x:R]``(f x)+l*(g x)`` a b).
Intros a b l f g; Unfold IsStepFun; Assert H := (pre f); Assert H0 := (pre g); Unfold IsStepFun in H H0; Elim H; Elim H0; Intros; Apply Specif.existT with (cons_ORlist x0 x); Apply StepFun_P27; Assumption.
Qed.

Lemma StepFun_P29 : (a,b:R;f:(StepFun a b)) (is_subdivision f a b (subdivision f)).
Intros a b f; Unfold is_subdivision; Apply existTT with (subdivision_val f); Apply StepFun_P1.
Qed.

Lemma StepFun_P30 : (a,b,l:R;f,g:(StepFun a b)) ``(RiemannInt_SF (mkStepFun (StepFun_P28 l f g)))==(RiemannInt_SF f)+l*(RiemannInt_SF g)``.
Intros a b l f g; Unfold RiemannInt_SF; Case (total_order_Rle a b); (Intro; Replace ``(Int_SF (subdivision_val (mkStepFun (StepFun_P28 l f g))) (subdivision (mkStepFun (StepFun_P28 l f g))))`` with (Int_SF (FF (cons_ORlist (subdivision f) (subdivision g)) [x:R]``(f x)+l*(g x)``) (cons_ORlist (subdivision f) (subdivision g))); [Rewrite StepFun_P19; Replace (Int_SF (FF (cons_ORlist (subdivision f) (subdivision g)) f) (cons_ORlist (subdivision f) (subdivision g))) with (Int_SF (subdivision_val f) (subdivision f)); [Replace (Int_SF (FF (cons_ORlist (subdivision f) (subdivision g)) g) (cons_ORlist (subdivision f) (subdivision g))) with (Int_SF (subdivision_val g) (subdivision g)); [Ring | Apply StepFun_P17 with (fe g) a b; [Apply StepFun_P1 | Apply StepFun_P21; Apply StepFun_P25 with (fe f); Apply StepFun_P29]] | Apply StepFun_P17 with (fe f) a b; [Apply StepFun_P1 | Apply StepFun_P21; Apply StepFun_P23 with (fe g); Apply StepFun_P29]] | Apply StepFun_P17 with [x:R]``(f x)+l*(g x)`` a b; [Apply StepFun_P21; Apply StepFun_P27; Apply StepFun_P29 | Apply (StepFun_P1 (mkStepFun (StepFun_P28 l f g)))]]).
Qed.

Lemma StepFun_P31 : (a,b:R;f:R->R;l,lf:Rlist) (adapted_couple f a b l lf) -> (adapted_couple [x:R](Rabsolu (f x)) a b l (app_Rlist lf Rabsolu)).
Unfold adapted_couple; Intros; Decompose [and] H; Clear H; Repeat Split; Try Assumption.
Symmetry; Rewrite H3; Rewrite RList_P18; Reflexivity.
Intros; Unfold constant_D_eq open_interval; Unfold constant_D_eq open_interval in H5; Intros; Rewrite (H5 ? H ? H4); Rewrite RList_P12; [Reflexivity | Rewrite H3 in H; Simpl in H; Apply H].
Qed.

Lemma StepFun_P32 : (a,b:R;f:(StepFun a b)) (IsStepFun [x:R](Rabsolu (f x)) a b).
Intros a b f; Unfold IsStepFun; Apply Specif.existT with (subdivision f); Unfold is_subdivision; Apply existTT with (app_Rlist (subdivision_val f) Rabsolu); Apply StepFun_P31; Apply StepFun_P1.
Qed.

Lemma StepFun_P33 : (l2,l1:Rlist) (ordered_Rlist l1) -> ``(Rabsolu (Int_SF l2 l1))<=(Int_SF (app_Rlist l2 Rabsolu) l1)``.
Induction l2; Intros.
Simpl; Rewrite Rabsolu_R0; Right; Reflexivity.
Simpl; Induction l1.
Rewrite Rabsolu_R0; Right; Reflexivity.
Induction l1.
Rewrite Rabsolu_R0; Right; Reflexivity.
Apply Rle_trans with ``(Rabsolu (r*(r2-r1)))+(Rabsolu (Int_SF r0 (cons r2 l1)))``.
Apply Rabsolu_triang.
Rewrite Rabsolu_mult; Rewrite (Rabsolu_right ``r2-r1``); [Apply Rle_compatibility; Apply H; Apply RList_P4 with r1; Assumption | Apply Rge_minus; Apply Rle_sym1; Apply (H0 O); Simpl; Apply lt_O_Sn].
Qed.

Lemma StepFun_P34 : (a,b:R;f:(StepFun a b)) ``a<=b`` -> ``(Rabsolu (RiemannInt_SF f))<=(RiemannInt_SF (mkStepFun (StepFun_P32 f)))``.
Intros; Unfold RiemannInt_SF; Case (total_order_Rle a b); Intro.
Replace (Int_SF (subdivision_val (mkStepFun (StepFun_P32 f))) (subdivision (mkStepFun (StepFun_P32 f)))) with (Int_SF (app_Rlist (subdivision_val f) Rabsolu) (subdivision f)).
Apply StepFun_P33; Assert H0 := (StepFun_P29 f); Unfold is_subdivision in H0; Elim H0; Intros; Unfold adapted_couple in p; Decompose [and] p; Assumption.
Apply StepFun_P17 with [x:R](Rabsolu (f x)) a b; [Apply StepFun_P31; Apply StepFun_P1 | Apply (StepFun_P1 (mkStepFun (StepFun_P32 f)))].
Elim n; Assumption.
Qed.

Lemma StepFun_P35 : (l:Rlist;a,b:R;f,g:R->R) (ordered_Rlist l) -> (pos_Rl l O)==a -> (pos_Rl l (pred (Rlength l)))==b -> ((x:R)``a<x<b``->``(f x)<=(g x)``) -> ``(Int_SF (FF l f) l)<=(Int_SF (FF l g) l)``.
Induction l; Intros.
Right; Reflexivity.
Simpl; Induction r0.
Right; Reflexivity.
Simpl; Apply Rplus_le.
Case (Req_EM r r0); Intro.
Rewrite H4; Right; Ring.
Do 2 Rewrite <- (Rmult_sym ``r0-r``); Apply Rle_monotony.
Apply Rle_sym2; Apply Rge_minus; Apply Rle_sym1; Apply (H0 O); Simpl; Apply lt_O_Sn.
Apply H3; Split.
Apply Rlt_monotony_contra with ``2``.
Sup0.
Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Assert H5 : r==a.
Apply H1.
Rewrite H5; Rewrite Rmult_1l; Rewrite double; Apply Rlt_compatibility.
Assert H6 := (H0 O (lt_O_Sn ?)).
Simpl in H6.
Elim H6; Intro.
Rewrite H5 in H7; Apply H7.
Elim H4; Assumption.
DiscrR.
Apply Rlt_monotony_contra with ``2``.
Sup0.
Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l; Rewrite double; Assert H5 : ``r0<=b``.
Replace b with (pos_Rl (cons r (cons r0 r1)) (pred (Rlength (cons r (cons r0 r1))))).
Replace r0 with (pos_Rl (cons r (cons r0 r1)) (S O)).
Elim (RList_P6 (cons r (cons r0 r1))); Intros; Apply H5.
Assumption.
Simpl; Apply le_n_S.
Apply le_O_n.
Simpl; Apply lt_n_Sn.
Reflexivity.
Apply Rle_lt_trans with ``r+b``.
Apply Rle_compatibility; Assumption.
Rewrite (Rplus_sym r); Apply Rlt_compatibility.
Apply Rlt_le_trans with r0.
Assert H6 := (H0 O (lt_O_Sn ?)).
Simpl in H6.
Elim H6; Intro.
Apply H7.
Elim H4; Assumption.
Assumption.
DiscrR.
Simpl in H; Apply H with r0 b.
Apply RList_P4 with r; Assumption.
Reflexivity.
Rewrite <- H2; Reflexivity.
Intros; Apply H3; Elim H4; Intros; Split; Try Assumption.
Apply Rle_lt_trans with r0; Try Assumption.
Rewrite <- H1.
Simpl; Apply (H0 O); Simpl; Apply lt_O_Sn.
Qed.

Lemma StepFun_P36 : (a,b:R;f,g:(StepFun a b);l:Rlist) ``a<=b`` -> (is_subdivision f a b l) -> (is_subdivision g a b l) -> ((x:R)``a<x<b``->``(f x)<=(g x)``) -> ``(RiemannInt_SF f) <= (RiemannInt_SF g)``.
Intros; Unfold RiemannInt_SF; Case (total_order_Rle a b); Intro.
Replace (Int_SF (subdivision_val f) (subdivision f)) with (Int_SF (FF l f) l).
Replace (Int_SF (subdivision_val g) (subdivision g)) with (Int_SF (FF l g) l).
Unfold is_subdivision in X; Elim X; Clear X; Intros; Unfold adapted_couple in p; Decompose [and] p; Clear p; Assert H5 : (Rmin a b)==a; [Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption] | Assert H7 : (Rmax a b)==b; [Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption] | Rewrite H5 in H3; Rewrite H7 in H2; EApply StepFun_P35 with a b; Assumption]].
Apply StepFun_P17 with (fe g) a b; [Apply StepFun_P21; Assumption | Apply StepFun_P1].
Apply StepFun_P17 with (fe f) a b; [Apply StepFun_P21; Assumption | Apply StepFun_P1].
Elim n; Assumption.
Qed.

Lemma StepFun_P37 : (a,b:R;f,g:(StepFun a b)) ``a<=b`` -> ((x:R)``a<x<b``->``(f x)<=(g x)``) -> ``(RiemannInt_SF f) <= (RiemannInt_SF g)``.
Intros; EApply StepFun_P36; Try Assumption.
EApply StepFun_P25; Apply StepFun_P29.
EApply StepFun_P23; Apply StepFun_P29.
Qed.

Lemma StepFun_P38 : (l:Rlist;a,b:R;f:R->R) (ordered_Rlist l) -> (pos_Rl l O)==a -> (pos_Rl l (pred (Rlength l)))==b -> (sigTT ? [g:(StepFun a b)](g b)==(f b)/\(i:nat)(lt i (pred (Rlength l)))->(constant_D_eq g (co_interval (pos_Rl l i) (pos_Rl l (S i))) (f (pos_Rl l i)))).
Intros l a b f; Generalize a; Clear a; NewInduction l. 
Intros a H H0 H1; Simpl in H0; Simpl in H1; Exists (mkStepFun (StepFun_P4 a b (f b))); Split.
Reflexivity.
Intros; Elim (lt_n_O ? H2).
Intros; NewDestruct l as [|r1 l].
Simpl in H1; Simpl in H0; Exists (mkStepFun (StepFun_P4 a b (f b))); Split.
Reflexivity.
Intros i H2; Elim (lt_n_O ? H2).
Intros; Assert H2 : (ordered_Rlist (cons r1 l)).
Apply RList_P4 with r; Assumption.
Assert H3 : (pos_Rl (cons r1 l) O)==r1.
Reflexivity.
Assert H4 : (pos_Rl (cons r1 l) (pred (Rlength (cons r1 l))))==b.
Rewrite <- H1; Reflexivity.
Elim (IHl r1 H2 H3 H4); Intros g [H5 H6].
Pose g' := [x:R]Cases (total_order_Rle r1 x) of
                      | (leftT _) => (g x)
                      | (rightT _) => (f a) end.
Assert H7 : ``r1<=b``.
Rewrite <- H4; Apply RList_P7; [Assumption | Left; Reflexivity].
Assert H8 : (IsStepFun g' a b).
Unfold IsStepFun; Assert H8 := (pre g); Unfold IsStepFun in H8; Elim H8; Intros lg H9; Unfold is_subdivision in H9; Elim H9; Clear H9; Intros lg2 H9; Split with (cons a lg); Unfold is_subdivision; Split with (cons (f a) lg2); Unfold adapted_couple in H9; Decompose [and] H9; Clear H9; Unfold adapted_couple; Repeat Split.
Unfold ordered_Rlist; Intros; Simpl in H9; Induction i.
Simpl; Rewrite H12; Replace (Rmin r1 b) with r1.
Simpl in H0; Rewrite <- H0; Apply (H O); Simpl; Apply lt_O_Sn.
Unfold Rmin; Case (total_order_Rle r1 b); Intro; [Reflexivity | Elim n; Assumption].
Apply (H10 i); Apply lt_S_n.
Replace (S (pred (Rlength lg))) with (Rlength lg).
Apply H9.
Apply S_pred with O; Apply neq_O_lt; Intro; Rewrite <- H14 in H9; Elim (lt_n_O ? H9).
Simpl; Assert H14 : ``a<=b``.
Rewrite <- H1; Simpl in H0; Rewrite <- H0; Apply RList_P7; [Assumption | Left; Reflexivity].
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Assert H14 : ``a<=b``.
Rewrite <- H1; Simpl in H0; Rewrite <- H0; Apply RList_P7; [Assumption | Left; Reflexivity].
Replace (Rmax a b) with (Rmax r1 b).
Rewrite <- H11; Induction lg.
Simpl in H13; Discriminate.
Reflexivity.
Unfold Rmax; Case (total_order_Rle a b); Case (total_order_Rle r1 b); Intros; Reflexivity Orelse Elim n; Assumption.
Simpl; Rewrite H13; Reflexivity.
Intros; Simpl in H9; Induction i.
Unfold constant_D_eq open_interval; Simpl; Intros; Assert H16 : (Rmin r1 b)==r1.
Unfold Rmin; Case (total_order_Rle r1 b); Intro; [Reflexivity | Elim n; Assumption].
Rewrite H16 in H12; Rewrite H12 in H14; Elim H14; Clear H14; Intros _ H14; Unfold g'; Case (total_order_Rle r1 x); Intro r3.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r3 H14)).
Reflexivity.
Change (constant_D_eq g' (open_interval (pos_Rl lg i) (pos_Rl lg (S i))) (pos_Rl lg2 i)); Clear Hreci; Assert H16 := (H15 i); Assert H17 : (lt i (pred (Rlength lg))).
Apply lt_S_n.
Replace (S (pred (Rlength lg))) with (Rlength lg).
Assumption.
Apply S_pred with O; Apply neq_O_lt; Red; Intro; Rewrite <- H14 in H9; Elim (lt_n_O ? H9).
Assert H18 := (H16 H17); Unfold constant_D_eq open_interval in H18; Unfold constant_D_eq open_interval; Intros; Assert H19 := (H18 ? H14); Rewrite <- H19; Unfold g'; Case (total_order_Rle r1 x); Intro.
Reflexivity.
Elim n; Replace r1 with (Rmin r1 b).
Rewrite <- H12; Elim H14; Clear H14; Intros H14 _; Left; Apply Rle_lt_trans with (pos_Rl lg i); Try Assumption.
Apply RList_P5.
Assumption.
Elim (RList_P3 lg (pos_Rl lg i)); Intros; Apply H21; Exists i; Split.
Reflexivity.
Apply lt_trans with (pred (Rlength lg)); Try Assumption.
Apply lt_pred_n_n; Apply neq_O_lt; Red; Intro; Rewrite <- H22 in H17; Elim (lt_n_O ? H17).
Unfold Rmin; Case (total_order_Rle r1 b); Intro; [Reflexivity | Elim n0; Assumption].
Exists (mkStepFun H8); Split.
Simpl; Unfold g'; Case (total_order_Rle r1 b); Intro.
Assumption.
Elim n; Assumption.
Intros; Simpl in H9; Induction i.
Unfold constant_D_eq co_interval; Simpl; Intros; Simpl in H0; Rewrite H0; Elim H10; Clear H10; Intros; Unfold g'; Case (total_order_Rle r1 x); Intro r3.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r3 H11)).
Reflexivity.
Clear Hreci; Change (constant_D_eq (mkStepFun H8) (co_interval (pos_Rl (cons r1 l) i) (pos_Rl (cons r1 l) (S i))) (f (pos_Rl (cons r1 l) i))); Assert H10 := (H6 i); Assert H11 : (lt i (pred (Rlength (cons r1 l)))).
Simpl; Apply lt_S_n; Assumption.
Assert H12 := (H10 H11); Unfold constant_D_eq co_interval in H12; Unfold constant_D_eq co_interval; Intros; Rewrite <- (H12 ? H13); Simpl; Unfold g'; Case (total_order_Rle r1 x); Intro.
Reflexivity.
Elim n; Elim H13; Clear H13; Intros; Apply Rle_trans with (pos_Rl (cons r1 l) i); Try Assumption; Change ``(pos_Rl (cons r1 l) O)<=(pos_Rl (cons r1 l) i)``; Elim (RList_P6 (cons r1 l)); Intros; Apply H15; [Assumption | Apply le_O_n | Simpl; Apply lt_trans with (Rlength l); [Apply lt_S_n; Assumption | Apply lt_n_Sn]].
Qed.

Lemma StepFun_P39 : (a,b:R;f:(StepFun a b)) (RiemannInt_SF f)==(Ropp (RiemannInt_SF (mkStepFun (StepFun_P6 (pre f))))).
Intros; Unfold RiemannInt_SF; Case (total_order_Rle a b); Case (total_order_Rle b a); Intros.
Assert H : (adapted_couple f a b (subdivision f) (subdivision_val f)); [Apply StepFun_P1 | Assert H0 : (adapted_couple (mkStepFun (StepFun_P6 (pre f))) b a (subdivision (mkStepFun (StepFun_P6 (pre f)))) (subdivision_val (mkStepFun (StepFun_P6 (pre f))))); [Apply StepFun_P1 | Assert H1 : a==b; [Apply Rle_antisym; Assumption | Rewrite (StepFun_P8 H H1); Assert H2 : b==a; [Symmetry; Apply H1 | Rewrite (StepFun_P8 H0 H2); Ring]]]].
Rewrite Ropp_Ropp; EApply StepFun_P17; [Apply StepFun_P1 | Apply StepFun_P2; Pose H := (StepFun_P6 (pre f)); Unfold IsStepFun in H; Elim H; Intros; Unfold is_subdivision; Elim p; Intros; Apply p0].
Apply eq_Ropp; EApply StepFun_P17; [Apply StepFun_P1 | Apply StepFun_P2; Pose H := (StepFun_P6 (pre f)); Unfold IsStepFun in H; Elim H; Intros; Unfold is_subdivision; Elim p; Intros; Apply p0].
Assert H : ``a<b``; [Auto with real | Assert H0 : ``b<a``; [Auto with real | Elim (Rlt_antirefl ? (Rlt_trans ? ? ? H H0))]].
Qed.

Lemma StepFun_P40 : (f:R->R;a,b,c:R;l1,l2,lf1,lf2:Rlist) ``a<b`` -> ``b<c`` -> (adapted_couple f a b l1 lf1) -> (adapted_couple f b c l2 lf2) -> (adapted_couple f a c (cons_Rlist l1 l2) (FF (cons_Rlist l1 l2) f)).
Intros f a b c l1 l2 lf1 lf2 H H0 H1 H2; Unfold adapted_couple in H1 H2; Unfold adapted_couple; Decompose [and] H1; Decompose [and] H2; Clear H1 H2; Repeat Split.
Apply RList_P25; Try Assumption.
Rewrite H10; Rewrite H4; Unfold Rmin Rmax; Case (total_order_Rle a b); Case (total_order_Rle b c); Intros; (Right; Reflexivity) Orelse (Elim n; Left; Assumption).
Rewrite RList_P22.
Rewrite H5; Unfold Rmin Rmax; Case (total_order_Rle a b); Case (total_order_Rle a c); Intros; [Reflexivity | Elim n; Apply Rle_trans with b; Left; Assumption | Elim n; Left; Assumption | Elim n0; Left; Assumption].
Red; Intro; Rewrite H1 in H6; Discriminate.
Rewrite RList_P24.
Rewrite H9; Unfold Rmin Rmax; Case (total_order_Rle b c); Case (total_order_Rle a c); Intros; [Reflexivity | Elim n; Apply Rle_trans with b; Left; Assumption | Elim n; Left; Assumption | Elim n0; Left; Assumption].
Red; Intro; Rewrite H1 in H11; Discriminate.
Apply StepFun_P20.
Rewrite RList_P23; Apply neq_O_lt; Red; Intro.
Assert H2 : (plus (Rlength l1) (Rlength l2))=O.
Symmetry; Apply H1.
Elim (plus_is_O ? ? H2); Intros; Rewrite H12 in H6; Discriminate.
Unfold constant_D_eq open_interval; Intros; Elim (le_or_lt (S (S i)) (Rlength l1)); Intro.
Assert H14 : (pos_Rl (cons_Rlist l1 l2) i) == (pos_Rl l1 i).
Apply RList_P26; Apply lt_S_n; Apply le_lt_n_Sm; Apply le_S_n; Apply le_trans with (Rlength l1); [Assumption | Apply le_n_Sn].
Assert H15 : (pos_Rl (cons_Rlist l1 l2) (S i))==(pos_Rl l1 (S i)).
Apply RList_P26; Apply lt_S_n; Apply le_lt_n_Sm; Assumption.
Rewrite H14 in H2; Rewrite H15 in H2; Assert H16 : (le (2) (Rlength l1)).
Apply le_trans with (S (S i)); [Repeat Apply le_n_S; Apply le_O_n | Assumption].
Elim (RList_P20 ? H16); Intros r1 [r2 [r3 H17]]; Rewrite H17; Change (f x)==(pos_Rl (app_Rlist (mid_Rlist (cons_Rlist (cons r2 r3) l2) r1) f) i); Rewrite RList_P12.
Induction i.
Simpl; Assert H18 := (H8 O); Unfold constant_D_eq open_interval in H18; Assert H19 : (lt O (pred (Rlength l1))).
Rewrite H17; Simpl; Apply lt_O_Sn.
Assert H20 := (H18 H19); Repeat Rewrite H20.
Reflexivity.
Assert H21 : ``r1<=r2``.
Rewrite H17 in H3; Apply (H3 O).
Simpl; Apply lt_O_Sn.
Elim H21; Intro.
Split.
Rewrite H17; Simpl; Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Apply Rlt_compatibility; Assumption | DiscrR]].
Rewrite H17; Simpl; Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite (Rplus_sym r1); Rewrite double; Apply Rlt_compatibility; Assumption | DiscrR]].
Elim H2; Intros; Rewrite H17 in H23; Rewrite H17 in H24; Simpl in H24; Simpl in H23; Rewrite H22 in H23; Elim (Rlt_antirefl ? (Rlt_trans ? ? ? H23 H24)).
Assumption.
Clear Hreci; Rewrite RList_P13.
Rewrite H17 in H14; Rewrite H17 in H15; Change (pos_Rl (cons_Rlist (cons r2 r3) l2) i)== (pos_Rl (cons r1 (cons r2 r3)) (S i)) in H14; Rewrite H14; Change (pos_Rl (cons_Rlist (cons r2 r3) l2) (S i))==(pos_Rl (cons r1 (cons r2 r3)) (S (S i))) in H15; Rewrite H15; Assert H18 := (H8 (S i)); Unfold constant_D_eq open_interval in H18; Assert H19 : (lt (S i) (pred (Rlength l1))).
Apply lt_pred; Apply lt_S_n; Apply le_lt_n_Sm; Assumption.
Assert H20 := (H18 H19); Repeat Rewrite H20.
Reflexivity.
Rewrite <- H17; Assert H21 : ``(pos_Rl l1 (S i))<=(pos_Rl l1 (S (S i)))``.
Apply (H3 (S i)); Apply lt_pred; Apply lt_S_n; Apply le_lt_n_Sm; Assumption.
Elim H21; Intro.
Split.
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Apply Rlt_compatibility; Assumption | DiscrR]].
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite (Rplus_sym (pos_Rl l1 (S i))); Rewrite double; Apply Rlt_compatibility; Assumption | DiscrR]].
Elim H2; Intros; Rewrite H22 in H23; Elim (Rlt_antirefl ? (Rlt_trans ? ? ? H23 H24)).
Assumption.
Simpl; Rewrite H17 in H1; Simpl in H1; Apply lt_S_n; Assumption.
Rewrite RList_P14; Rewrite H17 in H1; Simpl in H1; Apply H1.
Inversion H12.
Assert H16 : (pos_Rl (cons_Rlist l1 l2) (S i))==b.
Rewrite RList_P29.
Rewrite H15; Rewrite <- minus_n_n; Rewrite H10; Unfold Rmin; Case (total_order_Rle b c); Intro; [Reflexivity | Elim n; Left; Assumption].
Rewrite H15; Apply le_n.
Induction l1.
Simpl in H15; Discriminate.
Clear Hrecl1; Simpl in H1; Simpl; Apply lt_n_S; Assumption.
Assert H17 : (pos_Rl (cons_Rlist l1 l2) i)==b.
Rewrite RList_P26.
Replace i with (pred (Rlength l1)); [Rewrite H4; Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Left; Assumption] | Rewrite H15; Reflexivity].
Rewrite H15; Apply lt_n_Sn.
Rewrite H16 in H2; Rewrite H17 in H2; Elim H2; Intros; Elim (Rlt_antirefl ? (Rlt_trans ? ? ? H14 H18)).
Assert H16 : (pos_Rl (cons_Rlist l1 l2) i) == (pos_Rl l2 (minus i (Rlength l1))).
Apply RList_P29.
Apply le_S_n; Assumption.
Apply lt_le_trans with (pred (Rlength (cons_Rlist l1 l2))); [Assumption | Apply le_pred_n].
Assert H17 : (pos_Rl (cons_Rlist l1 l2) (S i))==(pos_Rl l2 (S (minus i (Rlength l1)))).
Replace (S (minus i (Rlength l1))) with (minus (S i) (Rlength l1)).
Apply RList_P29.
Apply le_S_n; Apply le_trans with (S i); [Assumption | Apply le_n_Sn].
Induction l1.
Simpl in H6; Discriminate.
Clear Hrecl1; Simpl in H1; Simpl; Apply lt_n_S; Assumption.
Symmetry; Apply minus_Sn_m; Apply le_S_n; Assumption.
Assert H18 : (le (2) (Rlength l1)).
Clear f c l2 lf2 H0 H3 H8 H7 H10 H9 H11 H13 i H1 x H2 H12 m H14 H15 H16 H17; Induction l1.
Discriminate.
Clear Hrecl1; Induction l1.
Simpl in H5; Simpl in H4; Assert H0 : ``(Rmin a b)<(Rmax a b)``.
Unfold Rmin Rmax; Case (total_order_Rle a b); Intro; [Assumption | Elim n; Left; Assumption].
Rewrite <- H5 in H0; Rewrite <- H4 in H0; Elim (Rlt_antirefl ? H0).
Clear Hrecl1; Simpl; Repeat Apply le_n_S; Apply le_O_n.
Elim (RList_P20 ? H18); Intros r1 [r2 [r3 H19]]; Rewrite H19; Change (f x)==(pos_Rl (app_Rlist (mid_Rlist (cons_Rlist (cons r2 r3) l2) r1) f) i); Rewrite RList_P12.
Induction i.
Assert H20 := (le_S_n ? ? H15); Assert H21 := (le_trans ? ? ? H18 H20); Elim (le_Sn_O ? H21).
Clear Hreci; Rewrite RList_P13.
Rewrite H19 in H16; Rewrite H19 in H17; Change (pos_Rl (cons_Rlist (cons r2 r3) l2) i)==  (pos_Rl l2 (minus (S i) (Rlength (cons r1 (cons r2 r3))))) in H16; Rewrite H16; Change (pos_Rl (cons_Rlist (cons r2 r3) l2) (S i))== (pos_Rl l2 (S (minus (S i) (Rlength (cons r1 (cons r2 r3)))))) in H17; Rewrite H17; Assert H20 := (H13 (minus (S i) (Rlength l1))); Unfold constant_D_eq open_interval in H20; Assert H21 : (lt (minus (S i) (Rlength l1)) (pred (Rlength l2))).
Apply lt_pred; Rewrite minus_Sn_m.
Apply simpl_lt_plus_l with (Rlength l1); Rewrite <- le_plus_minus.
Rewrite H19 in H1; Simpl in H1; Rewrite H19; Simpl; Rewrite RList_P23 in H1; Apply lt_n_S; Assumption.
Apply le_trans with (S i); [Apply le_S_n; Assumption | Apply le_n_Sn].
Apply le_S_n; Assumption.
Assert H22 := (H20 H21); Repeat Rewrite H22.
Reflexivity.
Rewrite <- H19; Assert H23 : ``(pos_Rl l2 (minus (S i) (Rlength l1)))<=(pos_Rl l2 (S (minus (S i) (Rlength l1))))``.
Apply H7; Apply lt_pred.
Rewrite minus_Sn_m.
Apply simpl_lt_plus_l with (Rlength l1); Rewrite <- le_plus_minus.
Rewrite H19 in H1; Simpl in H1; Rewrite H19; Simpl; Rewrite RList_P23 in H1; Apply lt_n_S; Assumption.
Apply le_trans with (S i); [Apply le_S_n; Assumption | Apply le_n_Sn].
Apply le_S_n; Assumption.
Elim H23; Intro.
Split.
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite double; Apply Rlt_compatibility; Assumption | DiscrR]].
Apply Rlt_monotony_contra with ``2``; [Sup0 | Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite (Rplus_sym (pos_Rl l2 (minus (S i) (Rlength l1)))); Rewrite double; Apply Rlt_compatibility; Assumption | DiscrR]].
Rewrite <- H19 in H16; Rewrite <- H19 in H17; Elim H2; Intros; Rewrite H19 in H25; Rewrite H19 in H26; Simpl in H25; Simpl in H16; Rewrite H16 in H25; Simpl in H26; Simpl in H17; Rewrite H17 in H26; Simpl in H24; Rewrite H24 in H25; Elim (Rlt_antirefl ? (Rlt_trans ? ? ? H25 H26)).
Assert H23 : (pos_Rl (cons_Rlist l1 l2) (S i))==(pos_Rl l2 (minus (S i) (Rlength l1))).
Rewrite H19; Simpl; Simpl in H16; Apply H16.
Assert H24 : (pos_Rl (cons_Rlist l1 l2) (S (S i)))==(pos_Rl l2 (S (minus (S i) (Rlength l1)))).
Rewrite H19; Simpl; Simpl in H17; Apply H17.
Rewrite <- H23; Rewrite <- H24; Assumption.
Simpl; Rewrite H19 in H1; Simpl in H1; Apply lt_S_n; Assumption.
Rewrite RList_P14; Rewrite H19 in H1; Simpl in H1; Simpl; Apply H1.
Qed.

Lemma StepFun_P41 : (f:R->R;a,b,c:R) ``a<=b``->``b<=c``->(IsStepFun f a b) -> (IsStepFun f b c) -> (IsStepFun f a c).
Unfold IsStepFun; Unfold is_subdivision; Intros; Elim X; Clear X; Intros l1 [lf1 H1]; Elim X0; Clear X0; Intros l2 [lf2 H2]; Case (total_order_T a b); Intro.
Elim s; Intro.
Case (total_order_T b c); Intro.
Elim s0; Intro.
Split with (cons_Rlist l1 l2); Split with (FF (cons_Rlist l1 l2) f); Apply StepFun_P40 with b lf1 lf2; Assumption.
Split with l1; Split with lf1; Rewrite b0 in H1; Assumption.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H0 r)).
Split with l2; Split with lf2; Rewrite <- b0 in H2; Assumption.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H r)).
Qed.

Lemma StepFun_P42 : (l1,l2:Rlist;f:R->R) (pos_Rl l1 (pred (Rlength l1)))==(pos_Rl l2 O) -> ``(Int_SF (FF (cons_Rlist l1 l2) f) (cons_Rlist l1 l2)) == (Int_SF (FF l1 f) l1) + (Int_SF (FF l2 f) l2)``.
Intros l1 l2 f; NewInduction l1 as [|r l1 IHl1]; Intros H; [ Simpl; Ring | NewDestruct l1; [Simpl in H; Simpl; NewDestruct l2; [Simpl; Ring | Simpl; Simpl in H; Rewrite H; Ring] | Simpl; Rewrite Rplus_assoc; Apply Rplus_plus_r; Apply IHl1; Rewrite <- H; Reflexivity]].
Qed.

Lemma StepFun_P43 : (f:R->R;a,b,c:R;pr1:(IsStepFun f a b);pr2:(IsStepFun f b c);pr3:(IsStepFun f a c)) ``(RiemannInt_SF (mkStepFun pr1))+(RiemannInt_SF (mkStepFun pr2))==(RiemannInt_SF (mkStepFun pr3))``.
Intros f; Intros; Assert H1 : (SigT ? [l:Rlist](sigTT ? [l0:Rlist](adapted_couple f a b l l0))).
Apply pr1.
Assert H2 : (SigT ? [l:Rlist](sigTT ? [l0:Rlist](adapted_couple f b c l l0))).
Apply pr2.
Assert H3 : (SigT ? [l:Rlist](sigTT ? [l0:Rlist](adapted_couple f a c l l0))).
Apply pr3.
Elim H1; Clear H1; Intros l1 [lf1 H1]; Elim H2; Clear H2; Intros l2 [lf2 H2]; Elim H3; Clear H3; Intros l3 [lf3 H3].
Replace (RiemannInt_SF (mkStepFun pr1)) with (Cases (total_order_Rle a b) of (leftT _) => (Int_SF lf1 l1) | (rightT _) => ``-(Int_SF lf1 l1)`` end).
Replace (RiemannInt_SF (mkStepFun pr2)) with (Cases (total_order_Rle b c) of (leftT _) => (Int_SF lf2 l2) | (rightT _) => ``-(Int_SF lf2 l2)`` end).
Replace (RiemannInt_SF (mkStepFun pr3)) with (Cases (total_order_Rle a c) of (leftT _) => (Int_SF lf3 l3) | (rightT _) => ``-(Int_SF lf3 l3)`` end).
Case (total_order_Rle a b); Case (total_order_Rle b c); Case (total_order_Rle a c); Intros.
Elim r1; Intro.
Elim r0; Intro.
Replace (Int_SF lf3 l3) with (Int_SF (FF (cons_Rlist l1 l2) f) (cons_Rlist l1 l2)).
Replace (Int_SF lf1 l1) with (Int_SF (FF l1 f) l1).
Replace (Int_SF lf2 l2) with (Int_SF (FF l2 f) l2).
Symmetry; Apply StepFun_P42.
Unfold adapted_couple in H1 H2; Decompose [and] H1; Decompose [and] H2; Clear H1 H2; Rewrite H11; Rewrite H5; Unfold Rmax Rmin; Case (total_order_Rle a b); Case (total_order_Rle b c); Intros; Reflexivity Orelse Elim n; Assumption.
EApply StepFun_P17; [Apply StepFun_P21; Unfold is_subdivision; Split with lf2; Apply H2; Assumption | Assumption].
EApply StepFun_P17; [Apply StepFun_P21; Unfold is_subdivision; Split with lf1; Apply H1 | Assumption].
EApply StepFun_P17; [Apply (StepFun_P40 H H0 H1 H2) | Apply H3].
Replace (Int_SF lf2 l2) with R0.
Rewrite Rplus_Or; EApply StepFun_P17; [Apply H1 | Rewrite <- H0 in H3; Apply H3].
Symmetry; EApply StepFun_P8; [Apply H2 | Assumption].
Replace (Int_SF lf1 l1) with R0.
Rewrite Rplus_Ol; EApply StepFun_P17; [Apply H2 | Rewrite H in H3; Apply H3].
Symmetry; EApply StepFun_P8; [Apply H1 | Assumption].
Elim n; Apply Rle_trans with b; Assumption.
Apply r_Rplus_plus with (Int_SF lf2 l2); Replace ``(Int_SF lf2 l2)+((Int_SF lf1 l1)+ -(Int_SF lf2 l2))`` with (Int_SF lf1 l1); [Idtac | Ring].
Assert H : ``c<b``.
Auto with real.
Elim r; Intro.
Rewrite Rplus_sym; Replace (Int_SF lf1 l1) with (Int_SF (FF (cons_Rlist l3 l2) f) (cons_Rlist l3 l2)).
Replace (Int_SF lf3 l3) with (Int_SF (FF l3 f) l3).
Replace (Int_SF lf2 l2) with (Int_SF (FF l2 f) l2).
Apply StepFun_P42.
Unfold adapted_couple in H2 H3; Decompose [and] H2; Decompose [and] H3; Clear H3 H2; Rewrite H10; Rewrite H6; Unfold Rmax Rmin; Case (total_order_Rle a c); Case (total_order_Rle b c); Intros; [Elim n; Assumption | Reflexivity | Elim n0; Assumption | Elim n1; Assumption].
EApply StepFun_P17; [Apply StepFun_P21; Unfold is_subdivision; Split with lf2; Apply H2 | Assumption].
EApply StepFun_P17; [Apply StepFun_P21; Unfold is_subdivision; Split with lf3; Apply H3 | Assumption].
EApply StepFun_P17; [Apply (StepFun_P40 H0 H H3 (StepFun_P2 H2)) | Apply H1].
Replace (Int_SF lf3 l3) with R0.
Rewrite Rplus_Or; EApply StepFun_P17; [Apply H1 | Apply StepFun_P2; Rewrite <- H0 in H2; Apply H2].
Symmetry; EApply StepFun_P8; [Apply H3 | Assumption].
Replace (Int_SF lf2 l2) with ``(Int_SF lf3 l3)+(Int_SF lf1 l1)``.
Ring.
Elim r; Intro.
Replace (Int_SF lf2 l2) with (Int_SF (FF (cons_Rlist l3 l1) f) (cons_Rlist l3 l1)).
Replace (Int_SF lf3 l3) with (Int_SF (FF l3 f) l3).
Replace (Int_SF lf1 l1) with (Int_SF (FF l1 f) l1).
Symmetry; Apply StepFun_P42.
Unfold adapted_couple in H1 H3; Decompose [and] H1; Decompose [and] H3; Clear H3 H1; Rewrite H9; Rewrite H5; Unfold Rmax Rmin; Case (total_order_Rle a c); Case (total_order_Rle a b); Intros; [Elim n; Assumption | Elim n1; Assumption | Reflexivity | Elim n1; Assumption].
EApply StepFun_P17; [Apply StepFun_P21; Unfold is_subdivision; Split with lf1; Apply H1 | Assumption].
EApply StepFun_P17; [Apply StepFun_P21; Unfold is_subdivision; Split with lf3; Apply H3 | Assumption].
EApply StepFun_P17.
Assert H0 : ``c<a``.
Auto with real.
Apply (StepFun_P40 H0 H (StepFun_P2 H3) H1).
Apply StepFun_P2; Apply H2.
Replace (Int_SF lf1 l1) with R0.
Rewrite Rplus_Or; EApply StepFun_P17; [Apply H3 | Rewrite <- H in H2; Apply H2].
Symmetry; EApply StepFun_P8; [Apply H1 | Assumption].
Assert H : ``b<a``.
Auto with real.
Replace (Int_SF lf2 l2) with ``(Int_SF lf3 l3)+(Int_SF lf1 l1)``.
Ring.
Rewrite Rplus_sym; Elim r; Intro.
Replace (Int_SF lf2 l2) with (Int_SF (FF (cons_Rlist l1 l3) f) (cons_Rlist l1 l3)).
Replace (Int_SF lf3 l3) with (Int_SF (FF l3 f) l3).
Replace (Int_SF lf1 l1) with (Int_SF (FF l1 f) l1).
Symmetry; Apply StepFun_P42.
Unfold adapted_couple in H1 H3; Decompose [and] H1; Decompose [and] H3; Clear H3 H1; Rewrite H11; Rewrite H5; Unfold Rmax Rmin; Case (total_order_Rle a c); Case (total_order_Rle a b); Intros; [Elim n; Assumption | Reflexivity | Elim n0; Assumption | Elim n1; Assumption].
EApply StepFun_P17; [Apply StepFun_P21; Unfold is_subdivision; Split with lf1; Apply H1 | Assumption].
EApply StepFun_P17; [Apply StepFun_P21; Unfold is_subdivision; Split with lf3; Apply H3 | Assumption].
EApply StepFun_P17.
Apply (StepFun_P40 H H0 (StepFun_P2 H1) H3).
Apply H2.
Replace (Int_SF lf3 l3) with R0.
Rewrite Rplus_Or; EApply StepFun_P17; [Apply H1 | Rewrite <- H0 in H2; Apply StepFun_P2; Apply H2].
Symmetry; EApply StepFun_P8; [Apply H3 | Assumption].
Assert H : ``c<a``.
Auto with real.
Replace (Int_SF lf1 l1) with ``(Int_SF lf2 l2)+(Int_SF lf3 l3)``.
Ring.
Elim r; Intro.
Replace (Int_SF lf1 l1) with (Int_SF (FF (cons_Rlist l2 l3) f) (cons_Rlist l2 l3)).
Replace (Int_SF lf3 l3) with (Int_SF (FF l3 f) l3).
Replace (Int_SF lf2 l2) with (Int_SF (FF l2 f) l2).
Symmetry; Apply StepFun_P42.
Unfold adapted_couple in H2 H3; Decompose [and] H2; Decompose [and] H3; Clear H3 H2; Rewrite H11; Rewrite H5; Unfold Rmax Rmin; Case (total_order_Rle a c); Case (total_order_Rle b c); Intros; [Elim n; Assumption | Elim n1; Assumption | Reflexivity | Elim n1; Assumption].
EApply StepFun_P17; [Apply StepFun_P21; Unfold is_subdivision; Split with lf2; Apply H2 | Assumption].
EApply StepFun_P17; [Apply StepFun_P21; Unfold is_subdivision; Split with lf3; Apply H3 | Assumption].
EApply StepFun_P17.
Apply (StepFun_P40 H0 H H2 (StepFun_P2 H3)).
Apply StepFun_P2; Apply H1.
Replace (Int_SF lf2 l2) with R0.
Rewrite Rplus_Ol; EApply StepFun_P17; [Apply H3 | Rewrite H0 in H1; Apply H1].
Symmetry; EApply StepFun_P8; [Apply H2 | Assumption].
Elim n; Apply Rle_trans with a; Try Assumption.
Auto with real.
Assert H : ``c<b``.
Auto with real.
Assert H0 : ``b<a``.
Auto with real.
Replace (Int_SF lf3 l3) with ``(Int_SF lf2 l2)+(Int_SF lf1 l1)``.
Ring.
Replace (Int_SF lf3 l3) with (Int_SF (FF (cons_Rlist l2 l1) f) (cons_Rlist l2 l1)).
Replace (Int_SF lf1 l1) with (Int_SF (FF l1 f) l1).
Replace (Int_SF lf2 l2) with (Int_SF (FF l2 f) l2).
Symmetry; Apply StepFun_P42.
Unfold adapted_couple in H2 H1; Decompose [and] H2; Decompose [and] H1; Clear H1 H2; Rewrite H11; Rewrite H5; Unfold Rmax Rmin; Case (total_order_Rle a b); Case (total_order_Rle b c); Intros; [Elim n1; Assumption | Elim n1; Assumption | Elim n0; Assumption | Reflexivity].
EApply StepFun_P17; [Apply StepFun_P21; Unfold is_subdivision; Split with lf2; Apply H2 | Assumption].
EApply StepFun_P17; [Apply StepFun_P21; Unfold is_subdivision; Split with lf1; Apply H1 | Assumption].
EApply StepFun_P17.
Apply (StepFun_P40 H H0 (StepFun_P2 H2) (StepFun_P2 H1)).
Apply StepFun_P2; Apply H3.
Unfold RiemannInt_SF; Case (total_order_Rle a c); Intro.
EApply StepFun_P17.
Apply H3.
Change (adapted_couple (mkStepFun pr3) a c (subdivision (mkStepFun 1!a 2!c 3!f pr3)) (subdivision_val (mkStepFun 1!a 2!c 3!f pr3))); Apply StepFun_P1.
Apply eq_Ropp; EApply StepFun_P17.
Apply H3.
Change (adapted_couple (mkStepFun pr3) a c (subdivision (mkStepFun 1!a 2!c 3!f pr3)) (subdivision_val (mkStepFun 1!a 2!c 3!f pr3))); Apply StepFun_P1.
Unfold RiemannInt_SF; Case (total_order_Rle b c); Intro.
EApply StepFun_P17.
Apply H2.
Change (adapted_couple (mkStepFun pr2) b c (subdivision (mkStepFun 1!b 2!c 3!f pr2)) (subdivision_val (mkStepFun 1!b 2!c 3!f pr2))); Apply StepFun_P1.
Apply eq_Ropp; EApply StepFun_P17.
Apply H2.
Change (adapted_couple (mkStepFun pr2) b c (subdivision (mkStepFun 1!b 2!c 3!f pr2)) (subdivision_val (mkStepFun 1!b 2!c 3!f pr2))); Apply StepFun_P1.
Unfold RiemannInt_SF; Case (total_order_Rle a b); Intro.
EApply StepFun_P17.
Apply H1.
Change (adapted_couple (mkStepFun pr1) a b (subdivision (mkStepFun 1!a 2!b 3!f pr1)) (subdivision_val (mkStepFun 1!a 2!b 3!f pr1))); Apply StepFun_P1.
Apply eq_Ropp; EApply StepFun_P17.
Apply H1.
Change (adapted_couple (mkStepFun pr1) a b (subdivision (mkStepFun 1!a 2!b 3!f pr1)) (subdivision_val (mkStepFun 1!a 2!b 3!f pr1))); Apply StepFun_P1.
Qed.

Lemma StepFun_P44 : (f:R->R;a,b,c:R) (IsStepFun f a b) -> ``a<=c<=b`` -> (IsStepFun f a c).
Intros f; Intros; Assert H0 : ``a<=b``.
Elim H; Intros; Apply Rle_trans with c; Assumption.
Elim H; Clear H; Intros; Unfold IsStepFun in X; Unfold is_subdivision in X; Elim X; Clear X; Intros l1 [lf1 H2]; Cut (l1,lf1:Rlist;a,b,c:R;f:R->R) (adapted_couple f a b l1 lf1) -> ``a<=c<=b`` -> (SigT ? [l:Rlist](sigTT ? [l0:Rlist](adapted_couple f a c l l0))).
Intros; Unfold IsStepFun; Unfold is_subdivision; EApply X.
Apply H2.
Split; Assumption.
Clear f a b c H0 H H1 H2 l1 lf1; Induction l1.
Intros; Unfold adapted_couple in H; Decompose [and] H; Clear H; Simpl in H4; Discriminate.
Induction r0.
Intros; Assert H1 : ``a==b``.
Unfold adapted_couple in H; Decompose [and] H; Clear H; Simpl in H3; Simpl in H2; Assert H7 : ``a<=b``.
Elim H0; Intros; Apply Rle_trans with c; Assumption.
Replace a with (Rmin a b).
Pattern 2 b; Replace b with (Rmax a b).
Rewrite <- H2; Rewrite H3; Reflexivity.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Split with (cons r nil); Split with lf1; Assert H2 : ``c==b``.
Rewrite H1 in H0; Elim H0; Intros; Apply Rle_antisym; Assumption.
Rewrite H2; Assumption.
Intros; Clear X; Induction lf1.
Unfold adapted_couple in H; Decompose [and] H; Clear H; Simpl in H4; Discriminate.
Clear Hreclf1; Assert H1 : (sumboolT ``c<=r1`` ``r1<c``).
Case (total_order_Rle c r1); Intro; [Left; Assumption | Right; Auto with real].
Elim H1; Intro.
Split with (cons r (cons c nil)); Split with (cons r3 nil); Unfold adapted_couple in H; Decompose [and] H; Clear H; Assert H6 : ``r==a``.
Simpl in H4; Rewrite H4; Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Elim H0; Intros; Apply Rle_trans with c; Assumption].
Elim H0; Clear H0; Intros; Unfold adapted_couple; Repeat Split.
Rewrite H6; Unfold ordered_Rlist; Intros; Simpl in H8; Inversion H8; [Simpl; Assumption | Elim (le_Sn_O ? H10)].
Simpl; Unfold Rmin; Case (total_order_Rle a c); Intro; [Assumption | Elim n; Assumption].
Simpl; Unfold Rmax; Case (total_order_Rle a c); Intro; [Reflexivity | Elim n; Assumption].
Unfold constant_D_eq open_interval; Intros; Simpl in H8; Inversion H8.
Simpl; Assert H10 := (H7 O); Assert H12 : (lt (0) (pred (Rlength (cons r (cons r1 r2))))).
Simpl; Apply lt_O_Sn.
Apply (H10 H12); Unfold open_interval; Simpl; Rewrite H11 in H9; Simpl in H9; Elim H9; Clear H9; Intros; Split; Try Assumption.
Apply Rlt_le_trans with c; Assumption.
Elim (le_Sn_O ? H11).
Cut (adapted_couple f r1 b (cons r1 r2) lf1).
Cut ``r1<=c<=b``.
Intros.
Elim (X0 ? ? ? ? ? H3 H2); Intros l1' [lf1' H4]; Split with (cons r l1'); Split with (cons r3 lf1'); Unfold adapted_couple in H H4; Decompose [and] H; Decompose [and] H4; Clear H H4 X0; Assert H14 : ``a<=b``.
Elim H0; Intros; Apply Rle_trans with c; Assumption.
Assert H16 : ``r==a``.
Simpl in H7; Rewrite H7; Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Induction l1'.
Simpl in H13; Discriminate.
Clear Hrecl1'; Unfold adapted_couple; Repeat Split.
Unfold ordered_Rlist; Intros; Simpl in H; Induction i.
Simpl; Replace r4 with r1.
Apply (H5 O).
Simpl; Apply lt_O_Sn.
Simpl in H12; Rewrite H12; Unfold Rmin; Case (total_order_Rle r1 c); Intro; [Reflexivity | Elim n; Left; Assumption].
Apply (H9 i); Simpl; Apply lt_S_n; Assumption.
Simpl; Unfold Rmin; Case (total_order_Rle a c); Intro; [Assumption | Elim n; Elim H0; Intros; Assumption].
Replace (Rmax a c) with (Rmax r1 c).
Rewrite <- H11; Reflexivity.
Unfold Rmax; Case (total_order_Rle r1 c); Case (total_order_Rle a c); Intros; [Reflexivity | Elim n; Elim H0; Intros; Assumption | Elim n; Left; Assumption | Elim n0; Left; Assumption].
Simpl; Simpl in H13; Rewrite H13; Reflexivity.
Intros; Simpl in H; Unfold constant_D_eq open_interval; Intros; Induction i.
Simpl; Assert H17 := (H10 O); Assert H18 : (lt (0) (pred (Rlength (cons r (cons r1 r2))))).
Simpl; Apply lt_O_Sn.
Apply (H17 H18); Unfold open_interval; Simpl; Simpl in H4; Elim H4; Clear H4; Intros; Split; Try Assumption; Replace r1 with r4.
Assumption.
Simpl in H12; Rewrite H12; Unfold Rmin; Case (total_order_Rle r1 c); Intro; [Reflexivity | Elim n; Left; Assumption].
Clear Hreci; Simpl; Apply H15.
Simpl; Apply lt_S_n; Assumption.
Unfold open_interval; Apply H4.
Split.
Left; Assumption.
Elim H0; Intros; Assumption.
EApply StepFun_P7; [Elim H0; Intros; Apply Rle_trans with c; [Apply H2 | Apply H3] | Apply H].
Qed.

Lemma StepFun_P45 : (f:R->R;a,b,c:R) (IsStepFun f a b) -> ``a<=c<=b`` -> (IsStepFun f c b).
Intros f; Intros; Assert H0 : ``a<=b``.
Elim H; Intros; Apply Rle_trans with c; Assumption.
Elim H; Clear H; Intros; Unfold IsStepFun in X; Unfold is_subdivision in X; Elim X; Clear X; Intros l1 [lf1 H2]; Cut (l1,lf1:Rlist;a,b,c:R;f:R->R) (adapted_couple f a b l1 lf1) -> ``a<=c<=b`` -> (SigT ? [l:Rlist](sigTT ? [l0:Rlist](adapted_couple f c b l l0))).
Intros; Unfold IsStepFun; Unfold is_subdivision; EApply X; [Apply H2 | Split; Assumption].
Clear f a b c H0 H H1 H2 l1 lf1; Induction l1.
Intros; Unfold adapted_couple in H; Decompose [and] H; Clear H; Simpl in H4; Discriminate.
Induction r0.
Intros; Assert H1 : ``a==b``.
Unfold adapted_couple in H; Decompose [and] H; Clear H; Simpl in H3; Simpl in H2; Assert H7 : ``a<=b``.
Elim H0; Intros; Apply Rle_trans with c; Assumption.
Replace a with (Rmin a b).
Pattern 2 b; Replace b with (Rmax a b).
Rewrite <- H2; Rewrite H3; Reflexivity.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Split with (cons r nil); Split with lf1; Assert H2 : ``c==b``.
Rewrite H1 in H0; Elim H0; Intros; Apply Rle_antisym; Assumption.
Rewrite <- H2 in H1; Rewrite <- H1; Assumption.
Intros; Clear X; Induction lf1.
Unfold adapted_couple in H; Decompose [and] H; Clear H; Simpl in H4; Discriminate.
Clear Hreclf1; Assert H1 : (sumboolT ``c<=r1`` ``r1<c``).
Case (total_order_Rle c r1); Intro; [Left; Assumption | Right; Auto with real].
Elim H1; Intro.
Split with (cons c (cons r1 r2)); Split with (cons r3 lf1); Unfold adapted_couple in H; Decompose [and] H; Clear H; Unfold adapted_couple; Repeat Split.
Unfold ordered_Rlist; Intros; Simpl in H; Induction i.
Simpl; Assumption.
Clear Hreci; Apply (H2 (S i)); Simpl; Assumption.
Simpl; Unfold Rmin; Case (total_order_Rle c b); Intro; [Reflexivity | Elim n; Elim H0; Intros; Assumption].
Replace (Rmax c b) with (Rmax a b).
Rewrite <- H3; Reflexivity.
Unfold Rmax; Case (total_order_Rle a b); Case (total_order_Rle c b); Intros; [Reflexivity | Elim n; Elim H0; Intros; Assumption | Elim n; Elim H0; Intros; Apply Rle_trans with c; Assumption | Elim n0; Elim H0; Intros; Apply Rle_trans with c; Assumption].
Simpl; Simpl in H5; Apply H5.
Intros; Simpl in H; Induction i.
Unfold constant_D_eq open_interval; Intros; Simpl; Apply (H7 O).
Simpl; Apply lt_O_Sn.
Unfold open_interval; Simpl; Simpl in H6; Elim H6; Clear H6; Intros; Split; Try Assumption; Apply Rle_lt_trans with c; Try Assumption; Replace r with a.
Elim H0; Intros; Assumption.
Simpl in H4; Rewrite H4; Unfold Rmin; Case (total_order_Rle a b); Intros; [Reflexivity | Elim n; Elim H0; Intros; Apply Rle_trans with c; Assumption].
Clear Hreci; Apply (H7 (S i)); Simpl; Assumption.
Cut (adapted_couple f r1 b (cons r1 r2) lf1).
Cut ``r1<=c<=b``.
Intros; Elim (X0 ? ? ? ? ? H3 H2); Intros l1' [lf1' H4]; Split with l1'; Split with lf1'; Assumption.
Split; [Left; Assumption | Elim H0; Intros; Assumption].
EApply StepFun_P7; [Elim H0; Intros; Apply Rle_trans with c; [Apply H2 | Apply H3] | Apply H].
Qed.

Lemma StepFun_P46 : (f:R->R;a,b,c:R) (IsStepFun f a b) -> (IsStepFun f b c) -> (IsStepFun f a c).
Intros f; Intros; Case (total_order_Rle a b); Case (total_order_Rle b c); Intros.
Apply StepFun_P41 with b; Assumption.
Case (total_order_Rle a c); Intro.
Apply StepFun_P44 with b; Try Assumption.
Split; [Assumption | Auto with real].
Apply StepFun_P6; Apply StepFun_P44 with b.
Apply StepFun_P6; Assumption.
Split; Auto with real.
Case (total_order_Rle a c); Intro.
Apply StepFun_P45 with b; Try Assumption.
Split; Auto with real.
Apply StepFun_P6; Apply StepFun_P45 with b.
Apply StepFun_P6; Assumption.
Split; [Assumption | Auto with real].
Apply StepFun_P6; Apply StepFun_P41 with b; Auto with real Orelse Apply StepFun_P6; Assumption.
Qed.
