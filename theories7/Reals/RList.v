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
V7only [ Import nat_scope. Import Z_scope. Import R_scope. ].
Open Local Scope R_scope.

Inductive Rlist : Type :=
| nil : Rlist
| cons : R -> Rlist -> Rlist.

Fixpoint In [x:R;l:Rlist] : Prop :=
Cases l of
| nil => False
| (cons a l') => ``x==a``\/(In x l') end.

Fixpoint Rlength [l:Rlist] : nat :=
Cases l of
| nil => O
| (cons a l') => (S (Rlength l')) end.

Fixpoint MaxRlist [l:Rlist] : R :=
 Cases l of
 | nil => R0
 | (cons a l1) => 
   Cases l1 of
   | nil => a
   | (cons a' l2) => (Rmax a (MaxRlist l1)) 
   end
end.

Fixpoint MinRlist [l:Rlist] : R :=
Cases l of
 | nil => R1 
 | (cons a l1) => 
   Cases l1 of
   | nil => a
   | (cons a' l2) => (Rmin a (MinRlist l1)) 
   end
end.

Lemma MaxRlist_P1 : (l:Rlist;x:R) (In x l)->``x<=(MaxRlist l)``.
Intros; Induction l.
Simpl in H; Elim H.
Induction l.
Simpl in H; Elim H; Intro.
Simpl; Right; Assumption.
Elim H0.
Replace (MaxRlist (cons r (cons r0 l))) with (Rmax r (MaxRlist (cons r0 l))).
Simpl in H; Decompose [or] H.
Rewrite H0; Apply RmaxLess1.
Unfold Rmax; Case (total_order_Rle r (MaxRlist (cons r0 l))); Intro.
Apply Hrecl; Simpl; Tauto.
Apply Rle_trans with (MaxRlist (cons r0 l)); [Apply Hrecl; Simpl; Tauto | Left; Auto with real].
Unfold Rmax; Case (total_order_Rle r (MaxRlist (cons r0 l))); Intro.
Apply Hrecl; Simpl; Tauto.
Apply Rle_trans with (MaxRlist (cons r0 l)); [Apply Hrecl; Simpl; Tauto | Left; Auto with real].
Reflexivity.
Qed.

Fixpoint AbsList [l:Rlist] : R->Rlist :=
[x:R] Cases l of
| nil => nil
| (cons a l') => (cons ``(Rabsolu (a-x))/2`` (AbsList l' x))
end.

Lemma MinRlist_P1 : (l:Rlist;x:R) (In x l)->``(MinRlist l)<=x``.
Intros; Induction l.
Simpl in H; Elim H.
Induction l.
Simpl in H; Elim H; Intro.
Simpl; Right; Symmetry; Assumption.
Elim H0.
Replace (MinRlist (cons r (cons r0 l))) with (Rmin r (MinRlist (cons r0 l))).
Simpl in H; Decompose [or] H.
Rewrite H0; Apply Rmin_l.
Unfold Rmin; Case (total_order_Rle r (MinRlist (cons r0 l))); Intro.
Apply Rle_trans with (MinRlist (cons r0 l)).
Assumption.
Apply Hrecl; Simpl; Tauto.
Apply Hrecl; Simpl; Tauto.
Apply Rle_trans with (MinRlist (cons r0 l)).
Apply Rmin_r.
Apply Hrecl; Simpl; Tauto.
Reflexivity.
Qed.

Lemma AbsList_P1 : (l:Rlist;x,y:R) (In y l) -> (In ``(Rabsolu (y-x))/2`` (AbsList l x)).
Intros; Induction l.
Elim H.
Simpl; Simpl in H; Elim H; Intro.
Left; Rewrite H0; Reflexivity.
Right; Apply Hrecl; Assumption.
Qed.

Lemma MinRlist_P2 : (l:Rlist) ((y:R)(In y l)->``0<y``)->``0<(MinRlist l)``.
Intros; Induction l.
Apply Rlt_R0_R1.
Induction l.
Simpl; Apply H; Simpl; Tauto.
Replace (MinRlist (cons r (cons r0 l))) with (Rmin r (MinRlist (cons r0 l))).
Unfold Rmin; Case (total_order_Rle r (MinRlist (cons r0 l))); Intro.
Apply H; Simpl; Tauto.
Apply Hrecl; Intros; Apply H; Simpl; Simpl in H0; Tauto.
Reflexivity.
Qed.

Lemma AbsList_P2 : (l:Rlist;x,y:R) (In y (AbsList l x)) -> (EXT z : R | (In z l)/\``y==(Rabsolu (z-x))/2``).
Intros; Induction l.
Elim H.
Elim H; Intro.
Exists r; Split.
Simpl; Tauto.
Assumption.
Assert H1 := (Hrecl H0); Elim H1; Intros; Elim H2; Clear H2; Intros; Exists x0; Simpl; Simpl in H2; Tauto.
Qed.

Lemma MaxRlist_P2 : (l:Rlist) (EXT y:R | (In y l)) -> (In (MaxRlist l) l).
Intros; Induction l.
Simpl in H; Elim H; Trivial.
Induction l.
Simpl; Left; Reflexivity.
Change (In (Rmax r (MaxRlist (cons r0 l))) (cons r (cons r0 l))); Unfold Rmax; Case (total_order_Rle r (MaxRlist (cons r0 l))); Intro.
Right; Apply Hrecl; Exists r0; Left; Reflexivity.
Left; Reflexivity.
Qed.

Fixpoint pos_Rl [l:Rlist] : nat->R :=
[i:nat] Cases l of
| nil => R0
| (cons a l') =>
 Cases i of
 | O => a
 | (S i') => (pos_Rl l' i')
 end
end.

Lemma pos_Rl_P1 : (l:Rlist;a:R) (lt O (Rlength l)) -> (pos_Rl (cons a l) (Rlength l))==(pos_Rl l (pred (Rlength l))).
Intros; Induction l; [Elim (lt_n_O ? H) | Simpl; Case (Rlength l); [Reflexivity | Intro; Reflexivity]].
Qed.

Lemma pos_Rl_P2 : (l:Rlist;x:R) (In x l)<->(EX i:nat | (lt i (Rlength l))/\x==(pos_Rl l i)).
Intros; Induction l.
Split; Intro; [Elim H | Elim H; Intros; Elim H0; Intros; Elim (lt_n_O ? H1)].
Split; Intro.
Elim H; Intro.
Exists O; Split; [Simpl; Apply lt_O_Sn | Simpl; Apply H0].
Elim Hrecl; Intros; Assert H3 := (H1 H0); Elim H3; Intros; Elim H4; Intros; Exists (S x0); Split; [Simpl; Apply lt_n_S; Assumption | Simpl; Assumption].
Elim H; Intros; Elim H0; Intros; Elim (zerop x0); Intro.
Rewrite a in H2; Simpl in H2; Left; Assumption.
Right; Elim Hrecl; Intros; Apply H4; Assert H5 : (S (pred x0))=x0.
Symmetry; Apply S_pred with O; Assumption.
Exists (pred x0); Split; [Simpl in H1; Apply lt_S_n; Rewrite H5; Assumption | Rewrite <- H5 in H2; Simpl in H2; Assumption].
Qed.

Lemma Rlist_P1 : (l:Rlist;P:R->R->Prop) ((x:R)(In x l)->(EXT y:R | (P x y))) -> (EXT l':Rlist | (Rlength l)=(Rlength l')/\(i:nat) (lt i (Rlength l))->(P (pos_Rl l i) (pos_Rl l' i))).
Intros; Induction l.
Exists nil; Intros; Split; [Reflexivity | Intros; Simpl in H0; Elim (lt_n_O ? H0)].
Assert H0 : (In r (cons r l)).
Simpl; Left; Reflexivity.
Assert H1 := (H ? H0); Assert H2 : (x:R)(In x l)->(EXT y:R | (P x y)).
Intros; Apply H; Simpl; Right; Assumption.
Assert H3 := (Hrecl H2); Elim H1; Intros; Elim H3; Intros; Exists (cons x x0); Intros; Elim H5; Clear H5; Intros; Split.
Simpl; Rewrite H5; Reflexivity.
Intros; Elim (zerop i); Intro.
Rewrite a; Simpl; Assumption.
Assert H8 : i=(S (pred i)).
Apply S_pred with O; Assumption.
Rewrite H8; Simpl; Apply H6; Simpl in H7; Apply lt_S_n; Rewrite <- H8; Assumption.
Qed.

Definition ordered_Rlist [l:Rlist] : Prop := (i:nat) (lt i (pred (Rlength l))) -> (Rle (pos_Rl l i) (pos_Rl l (S i))).

Fixpoint insert [l:Rlist] : R->Rlist :=
[x:R] Cases l of
| nil => (cons x nil)
| (cons a l') =>
 Cases (total_order_Rle a x) of
 | (leftT _) => (cons a (insert l' x))
 | (rightT _) => (cons x l)
 end
end.

Fixpoint cons_Rlist [l:Rlist] : Rlist->Rlist :=
[k:Rlist] Cases l of
| nil => k
| (cons a l') => (cons a (cons_Rlist l' k)) end.

Fixpoint cons_ORlist [k:Rlist] : Rlist->Rlist :=
[l:Rlist] Cases k of
| nil => l
| (cons a k') => (cons_ORlist k' (insert l a))
end.

Fixpoint app_Rlist [l:Rlist] : (R->R)->Rlist :=
[f:R->R] Cases l of
| nil => nil
| (cons a l') => (cons (f a) (app_Rlist l' f))
end.

Fixpoint mid_Rlist [l:Rlist] : R->Rlist :=
[x:R] Cases l of
| nil => nil
| (cons a l') => (cons ``(x+a)/2`` (mid_Rlist l' a))
end.

Definition Rtail [l:Rlist] : Rlist :=
Cases l of
| nil => nil
| (cons a l') => l'
end.

Definition FF [l:Rlist;f:R->R] : Rlist := 
Cases l of
| nil => nil
| (cons a l') => (app_Rlist (mid_Rlist l' a) f)
end.

Lemma RList_P0 : (l:Rlist;a:R) ``(pos_Rl (insert l a) O) == a`` \/ ``(pos_Rl (insert l a) O) == (pos_Rl l O)``.
Intros; Induction l; [Left; Reflexivity | Simpl; Case (total_order_Rle r a); Intro; [Right; Reflexivity | Left; Reflexivity]].
Qed.

Lemma RList_P1 : (l:Rlist;a:R) (ordered_Rlist l) -> (ordered_Rlist (insert l a)).
Intros; Induction l.
Simpl; Unfold ordered_Rlist; Intros; Simpl in H0; Elim (lt_n_O ? H0).
Simpl; Case (total_order_Rle r a); Intro.
Assert H1 : (ordered_Rlist l).
Unfold ordered_Rlist; Unfold ordered_Rlist in H; Intros; Assert H1 : (lt (S i) (pred (Rlength (cons r l)))); [Simpl; Replace (Rlength l) with (S (pred (Rlength l))); [Apply lt_n_S; Assumption | Symmetry; Apply S_pred with O; Apply neq_O_lt; Red; Intro; Rewrite <- H1 in H0; Simpl in H0; Elim (lt_n_O ? H0)] | Apply (H ? H1)].
Assert H2 := (Hrecl H1); Unfold ordered_Rlist; Intros; Induction i.
Simpl; Assert H3 := (RList_P0 l a); Elim H3; Intro.
Rewrite H4; Assumption.
Induction l; [Simpl; Assumption | Rewrite H4; Apply (H O); Simpl; Apply lt_O_Sn].
Simpl; Apply H2; Simpl in H0; Apply lt_S_n; Replace (S (pred (Rlength (insert l a)))) with (Rlength (insert l a)); [Assumption | Apply S_pred with O; Apply neq_O_lt; Red; Intro; Rewrite <- H3 in H0; Elim (lt_n_O ? H0)].
Unfold ordered_Rlist; Intros; Induction i; [Simpl; Auto with real | Change ``(pos_Rl (cons r l) i)<=(pos_Rl (cons r l) (S i))``; Apply H; Simpl in H0; Simpl; Apply (lt_S_n ? ? H0)].
Qed.

Lemma RList_P2 : (l1,l2:Rlist) (ordered_Rlist l2) ->(ordered_Rlist (cons_ORlist l1 l2)).
Induction l1; [Intros; Simpl; Apply H | Intros; Simpl; Apply H; Apply RList_P1; Assumption].
Qed.

Lemma RList_P3 : (l:Rlist;x:R) (In x l) <-> (EX i:nat | x==(pos_Rl l i)/\(lt i (Rlength l))).
Intros; Split; Intro; Induction l.
Elim H.
Elim H; Intro; [Exists O; Split; [Apply H0 | Simpl; Apply lt_O_Sn] | Elim (Hrecl H0); Intros; Elim H1; Clear H1; Intros; Exists (S x0); Split; [Apply H1 | Simpl; Apply lt_n_S; Assumption]].
Elim H; Intros; Elim H0; Intros; Elim (lt_n_O ? H2).
Simpl; Elim H; Intros; Elim H0; Clear H0; Intros; Induction x0; [Left; Apply H0 | Right; Apply Hrecl; Exists x0; Split; [Apply H0 | Simpl in H1; Apply lt_S_n; Assumption]].
Qed.

Lemma RList_P4 : (l1:Rlist;a:R) (ordered_Rlist (cons a l1)) -> (ordered_Rlist l1).
Intros; Unfold ordered_Rlist; Intros; Apply (H (S i)); Simpl; Replace (Rlength l1) with (S (pred (Rlength l1))); [Apply lt_n_S; Assumption | Symmetry; Apply S_pred with O; Apply neq_O_lt; Red; Intro; Rewrite <- H1 in H0; Elim (lt_n_O ? H0)].
Qed.

Lemma RList_P5 : (l:Rlist;x:R) (ordered_Rlist l) -> (In x l) -> ``(pos_Rl l O)<=x``.
Intros; Induction l; [Elim H0 | Simpl; Elim H0; Intro; [Rewrite H1; Right; Reflexivity | Apply Rle_trans with (pos_Rl l O); [Apply (H O); Simpl; Induction l; [Elim H1 | Simpl; Apply lt_O_Sn] | Apply Hrecl; [EApply RList_P4; Apply H | Assumption]]]].
Qed.

Lemma RList_P6 : (l:Rlist) (ordered_Rlist l)<->((i,j:nat)(le i j)->(lt j (Rlength l))->``(pos_Rl l i)<=(pos_Rl l j)``).
Induction l; Split; Intro.
Intros; Right; Reflexivity.
Unfold ordered_Rlist; Intros; Simpl in H0; Elim (lt_n_O ? H0).
Intros; Induction i; [Induction j; [Right; Reflexivity | Simpl; Apply Rle_trans with (pos_Rl r0 O); [Apply (H0 O); Simpl; Simpl in H2; Apply neq_O_lt; Red; Intro; Rewrite <- H3 in H2; Assert H4 := (lt_S_n ? ? H2); Elim (lt_n_O ? H4) | Elim H; Intros; Apply H3; [Apply RList_P4 with r; Assumption | Apply le_O_n | Simpl in H2; Apply lt_S_n; Assumption]]] | Induction j; [Elim (le_Sn_O ? H1) | Simpl; Elim H; Intros; Apply H3; [Apply RList_P4 with r; Assumption | Apply le_S_n; Assumption | Simpl in H2; Apply lt_S_n; Assumption]]].
Unfold ordered_Rlist; Intros; Apply H0; [Apply le_n_Sn | Simpl; Simpl in H1; Apply lt_n_S; Assumption].
Qed.

Lemma RList_P7 : (l:Rlist;x:R) (ordered_Rlist l) -> (In x l) -> ``x<=(pos_Rl l (pred (Rlength l)))``.
Intros; Assert H1 := (RList_P6 l); Elim H1; Intros H2 _; Assert H3 := (H2 H); Clear H1 H2; Assert H1 := (RList_P3 l x); Elim H1; Clear H1; Intros; Assert H4 := (H1 H0); Elim H4; Clear H4; Intros; Elim H4; Clear H4; Intros; Rewrite H4; Assert H6 : (Rlength l)=(S (pred (Rlength l))).
Apply S_pred with O; Apply neq_O_lt; Red; Intro; Rewrite <- H6 in H5; Elim (lt_n_O ? H5).
Apply H3; [Rewrite H6 in H5; Apply lt_n_Sm_le; Assumption | Apply lt_pred_n_n; Apply neq_O_lt; Red; Intro; Rewrite <- H7 in H5; Elim (lt_n_O ? H5)].
Qed.

Lemma RList_P8 : (l:Rlist;a,x:R) (In x (insert l a)) <-> x==a\/(In x l).
Induction l.
Intros; Split; Intro; Simpl in H; Apply H.
Intros; Split; Intro; [Simpl in H0; Generalize H0; Case (total_order_Rle r a); Intros; [Simpl in H1; Elim H1; Intro; [Right; Left; Assumption |Elim (H a x); Intros; Elim (H3 H2); Intro; [Left; Assumption | Right; Right; Assumption]] | Simpl in H1; Decompose [or] H1; [Left; Assumption | Right; Left; Assumption | Right; Right; Assumption]]  |  Simpl; Case (total_order_Rle r a); Intro; [Simpl in H0; Decompose [or] H0; [Right; Elim (H a x); Intros; Apply H3; Left | Left | Right; Elim (H a x); Intros; Apply H3; Right] | Simpl in H0; Decompose [or] H0; [Left | Right; Left | Right; Right]]; Assumption].
Qed.

Lemma RList_P9 : (l1,l2:Rlist;x:R) (In x (cons_ORlist l1 l2)) <-> (In x l1)\/(In x l2).
Induction l1.
Intros; Split; Intro; [Simpl in H; Right; Assumption | Simpl; Elim H; Intro; [Elim H0 | Assumption]].
Intros; Split.
Simpl; Intros; Elim (H (insert l2 r) x); Intros; Assert H3 := (H1 H0); Elim H3; Intro; [Left; Right; Assumption | Elim (RList_P8 l2 r x); Intros H5 _; Assert H6 := (H5 H4); Elim H6; Intro; [Left; Left; Assumption | Right; Assumption]].
Intro; Simpl; Elim (H (insert l2 r) x); Intros _ H1; Apply H1; Elim H0; Intro; [Elim H2; Intro; [Right; Elim (RList_P8 l2 r x); Intros _ H4; Apply H4; Left; Assumption | Left; Assumption] | Right; Elim (RList_P8 l2 r x); Intros _ H3; Apply H3; Right; Assumption].
Qed.

Lemma RList_P10 : (l:Rlist;a:R) (Rlength (insert l a))==(S (Rlength l)).
Intros; Induction l; [Reflexivity | Simpl; Case (total_order_Rle r a); Intro; [Simpl; Rewrite Hrecl; Reflexivity | Reflexivity]].
Qed.

Lemma RList_P11 : (l1,l2:Rlist) (Rlength (cons_ORlist l1 l2))=(plus (Rlength l1) (Rlength l2)).
Induction l1; [Intro; Reflexivity | Intros; Simpl; Rewrite (H (insert l2 r)); Rewrite RList_P10; Apply INR_eq; Rewrite S_INR; Do 2 Rewrite plus_INR; Rewrite S_INR; Ring].
Qed.

Lemma RList_P12 : (l:Rlist;i:nat;f:R->R) (lt i (Rlength l)) -> (pos_Rl (app_Rlist l f) i)==(f (pos_Rl l i)).
Induction l; [Intros; Elim (lt_n_O ? H) | Intros; Induction i; [Reflexivity | Simpl; Apply H; Apply lt_S_n; Apply H0]].
Qed.

Lemma RList_P13 : (l:Rlist;i:nat;a:R) (lt i (pred (Rlength l))) -> ``(pos_Rl (mid_Rlist l a) (S i)) == ((pos_Rl l i)+(pos_Rl l (S i)))/2``.
Induction l.
Intros; Simpl in H; Elim (lt_n_O ? H).
Induction r0.
Intros; Simpl in H0; Elim (lt_n_O ? H0).
Intros; Simpl in H1; Induction i.
Reflexivity.
Change ``(pos_Rl (mid_Rlist (cons r1 r2) r) (S i)) == ((pos_Rl (cons r1 r2) i)+(pos_Rl (cons r1 r2) (S i)))/2``; Apply H0; Simpl; Apply lt_S_n; Assumption.
Qed.

Lemma RList_P14 : (l:Rlist;a:R) (Rlength (mid_Rlist l a))=(Rlength l).
Induction l; Intros; [Reflexivity | Simpl; Rewrite (H r); Reflexivity].
Qed.

Lemma RList_P15 : (l1,l2:Rlist) (ordered_Rlist l1) -> (ordered_Rlist l2) -> (pos_Rl l1 O)==(pos_Rl l2 O) -> (pos_Rl (cons_ORlist l1 l2) O)==(pos_Rl l1 O).
Intros; Apply Rle_antisym.
Induction l1; [Simpl; Simpl in H1; Right; Symmetry; Assumption | Elim (RList_P9 (cons r l1) l2 (pos_Rl (cons r l1) (0))); Intros; Assert H4 : (In (pos_Rl (cons r l1) (0)) (cons r l1))\/(In (pos_Rl (cons r l1) (0)) l2); [Left; Left; Reflexivity | Assert H5 := (H3 H4); Apply RList_P5; [Apply RList_P2; Assumption | Assumption]]].
Induction l1; [Simpl; Simpl in H1; Right; Assumption | Assert H2 : (In (pos_Rl (cons_ORlist (cons r l1) l2) (0)) (cons_ORlist (cons r l1) l2)); [Elim (RList_P3 (cons_ORlist (cons r l1) l2) (pos_Rl (cons_ORlist (cons r l1) l2) (0))); Intros; Apply H3; Exists O; Split; [Reflexivity | Rewrite RList_P11; Simpl; Apply lt_O_Sn] | Elim (RList_P9 (cons r l1) l2 (pos_Rl (cons_ORlist (cons r l1) l2) (0))); Intros; Assert H5 := (H3 H2); Elim H5; Intro; [Apply RList_P5; Assumption | Rewrite H1; Apply RList_P5; Assumption]]].
Qed.

Lemma RList_P16 : (l1,l2:Rlist) (ordered_Rlist l1) -> (ordered_Rlist l2) -> (pos_Rl l1 (pred (Rlength l1)))==(pos_Rl l2 (pred (Rlength l2))) -> (pos_Rl (cons_ORlist l1 l2) (pred (Rlength (cons_ORlist l1 l2))))==(pos_Rl l1 (pred (Rlength l1))).
Intros; Apply Rle_antisym.
Induction l1.
Simpl; Simpl in H1; Right; Symmetry; Assumption. 
Assert H2 : (In (pos_Rl (cons_ORlist (cons r l1) l2) (pred (Rlength (cons_ORlist (cons r l1) l2)))) (cons_ORlist (cons r l1) l2)); [Elim (RList_P3 (cons_ORlist (cons r l1) l2) (pos_Rl (cons_ORlist (cons r l1) l2) (pred (Rlength (cons_ORlist (cons r l1) l2))))); Intros; Apply H3; Exists (pred (Rlength (cons_ORlist (cons r l1) l2))); Split; [Reflexivity | Rewrite RList_P11; Simpl; Apply lt_n_Sn] | Elim (RList_P9 (cons r l1) l2 (pos_Rl (cons_ORlist (cons r l1) l2) (pred (Rlength (cons_ORlist (cons r l1) l2))))); Intros; Assert H5 := (H3 H2); Elim H5; Intro; [Apply RList_P7; Assumption | Rewrite H1; Apply RList_P7; Assumption]].
Induction l1.
Simpl; Simpl in H1; Right; Assumption.
Elim (RList_P9 (cons r l1) l2 (pos_Rl (cons r l1) (pred (Rlength (cons r l1))))); Intros; Assert H4 : (In (pos_Rl (cons r l1) (pred (Rlength (cons r l1)))) (cons r l1))\/(In (pos_Rl (cons r l1) (pred (Rlength (cons r l1)))) l2); [Left; Change (In (pos_Rl (cons r l1) (Rlength l1)) (cons r l1)); Elim (RList_P3 (cons r l1) (pos_Rl (cons r l1) (Rlength l1))); Intros; Apply H5; Exists (Rlength l1); Split; [Reflexivity | Simpl; Apply lt_n_Sn] | Assert H5 := (H3 H4); Apply RList_P7; [Apply RList_P2; Assumption | Elim (RList_P9 (cons r l1) l2 (pos_Rl (cons r l1) (pred (Rlength (cons r l1))))); Intros; Apply H7; Left; Elim (RList_P3 (cons r l1) (pos_Rl (cons r l1) (pred (Rlength (cons r l1))))); Intros; Apply H9; Exists (pred (Rlength (cons r l1))); Split; [Reflexivity | Simpl; Apply lt_n_Sn]]].
Qed.

Lemma RList_P17 : (l1:Rlist;x:R;i:nat) (ordered_Rlist l1) -> (In x l1) -> ``(pos_Rl l1 i)<x`` -> (lt i (pred (Rlength l1))) -> ``(pos_Rl l1 (S i))<=x``.
Induction l1.
Intros; Elim H0.
Intros; Induction i.
Simpl; Elim H1; Intro; [Simpl in H2; Rewrite H4 in H2; Elim (Rlt_antirefl ? H2) | Apply RList_P5; [Apply RList_P4 with r; Assumption | Assumption]].
Simpl; Simpl in H2; Elim H1; Intro.
Rewrite H4 in H2; Assert H5 : ``r<=(pos_Rl r0 i)``; [Apply Rle_trans with (pos_Rl r0 O); [Apply (H0 O); Simpl; Simpl in H3; Apply neq_O_lt; Red; Intro; Rewrite <- H5 in H3; Elim (lt_n_O ? H3) | Elim (RList_P6 r0); Intros; Apply H5; [Apply RList_P4 with r; Assumption | Apply le_O_n | Simpl in H3; Apply lt_S_n; Apply lt_trans with (Rlength r0); [Apply H3 | Apply lt_n_Sn]]] | Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H5 H2))].
Apply H; Try Assumption; [Apply RList_P4 with r; Assumption | Simpl in H3; Apply lt_S_n; Replace (S (pred (Rlength r0))) with (Rlength r0); [Apply H3 | Apply S_pred with O; Apply neq_O_lt; Red; Intro; Rewrite <- H5 in H3; Elim (lt_n_O ? H3)]].
Qed.

Lemma RList_P18 : (l:Rlist;f:R->R) (Rlength (app_Rlist l f))=(Rlength l).
Induction l; Intros; [Reflexivity | Simpl; Rewrite H; Reflexivity].
Qed.

Lemma RList_P19 : (l:Rlist) ~l==nil -> (EXT r:R | (EXT r0:Rlist | l==(cons r r0))).
Intros; Induction l; [Elim H; Reflexivity | Exists r; Exists l; Reflexivity].
Qed.

Lemma RList_P20 : (l:Rlist) (le (2) (Rlength l)) -> (EXT r:R | (EXT r1:R | (EXT l':Rlist | l==(cons r (cons r1 l'))))). 
Intros; Induction l; [Simpl in H; Elim (le_Sn_O ? H) | Induction l; [Simpl in H; Elim (le_Sn_O ? (le_S_n ? ? H)) | Exists r; Exists r0; Exists l; Reflexivity]].
Qed.

Lemma RList_P21 : (l,l':Rlist) l==l' -> (Rtail l)==(Rtail l').
Intros; Rewrite H; Reflexivity.
Qed.

Lemma RList_P22 : (l1,l2:Rlist) ~l1==nil -> (pos_Rl (cons_Rlist l1 l2) O)==(pos_Rl l1 O).
Induction l1; [Intros; Elim H; Reflexivity | Intros; Reflexivity].
Qed.

Lemma RList_P23 : (l1,l2:Rlist) (Rlength (cons_Rlist l1 l2))==(plus (Rlength l1) (Rlength l2)).
Induction l1; [Intro; Reflexivity | Intros; Simpl; Rewrite H; Reflexivity].
Qed.

Lemma RList_P24 : (l1,l2:Rlist) ~l2==nil -> (pos_Rl (cons_Rlist l1 l2) (pred (Rlength (cons_Rlist l1 l2)))) == (pos_Rl l2 (pred (Rlength l2))).
Induction l1.
Intros; Reflexivity.
Intros; Rewrite <- (H l2 H0); Induction l2.
Elim H0; Reflexivity.
Do 2 Rewrite RList_P23; Replace (plus (Rlength (cons r r0)) (Rlength (cons r1 l2))) with (S (S (plus (Rlength r0) (Rlength l2)))); [Replace (plus (Rlength r0) (Rlength (cons r1 l2))) with (S (plus (Rlength r0) (Rlength l2))); [Reflexivity | Simpl; Apply INR_eq; Rewrite S_INR; Do 2 Rewrite plus_INR; Rewrite S_INR; Ring] | Simpl; Apply INR_eq; Do 3 Rewrite S_INR; Do 2 Rewrite plus_INR; Rewrite S_INR; Ring].
Qed.

Lemma RList_P25 : (l1,l2:Rlist) (ordered_Rlist l1) -> (ordered_Rlist l2) -> ``(pos_Rl l1 (pred (Rlength l1)))<=(pos_Rl l2 O)`` -> (ordered_Rlist (cons_Rlist l1 l2)).
Induction l1.
Intros; Simpl; Assumption.
Induction r0.
Intros; Simpl; Simpl in H2; Unfold ordered_Rlist; Intros; Simpl in H3.
Induction i.
Simpl; Assumption.
Change ``(pos_Rl l2 i)<=(pos_Rl l2 (S i))``; Apply (H1 i); Apply lt_S_n; Replace (S (pred (Rlength l2))) with (Rlength l2); [Assumption | Apply S_pred with O; Apply neq_O_lt; Red; Intro; Rewrite <- H4 in H3; Elim (lt_n_O ? H3)].
Intros; Clear H; Assert H : (ordered_Rlist (cons_Rlist (cons r1 r2) l2)).
Apply H0; Try Assumption.
Apply RList_P4 with r; Assumption.
Unfold ordered_Rlist; Intros; Simpl in H4; Induction i.
Simpl; Apply (H1 O); Simpl; Apply lt_O_Sn.
Change ``(pos_Rl (cons_Rlist (cons r1 r2) l2) i)<=(pos_Rl (cons_Rlist (cons r1 r2) l2) (S i))``; Apply (H i); Simpl; Apply lt_S_n; Assumption.
Qed.

Lemma RList_P26 : (l1,l2:Rlist;i:nat) (lt i (Rlength l1)) -> (pos_Rl (cons_Rlist l1 l2) i)==(pos_Rl l1 i).
Induction l1.
Intros; Elim (lt_n_O ? H).
Intros; Induction i.
Apply RList_P22; Discriminate.
Apply (H l2 i); Simpl in H0; Apply lt_S_n; Assumption.
Qed.

Lemma RList_P27 : (l1,l2,l3:Rlist) (cons_Rlist l1 (cons_Rlist l2 l3))==(cons_Rlist (cons_Rlist l1 l2) l3).
Induction l1; Intros; [Reflexivity | Simpl; Rewrite (H l2 l3); Reflexivity].
Qed.

Lemma RList_P28 : (l:Rlist) (cons_Rlist l nil)==l.
Induction l; [Reflexivity | Intros; Simpl; Rewrite H; Reflexivity].
Qed.

Lemma RList_P29 : (l2,l1:Rlist;i:nat) (le (Rlength l1) i) -> (lt i (Rlength (cons_Rlist l1 l2))) -> (pos_Rl (cons_Rlist l1 l2) i)==(pos_Rl l2 (minus i (Rlength l1))).
Induction l2.
Intros; Rewrite RList_P28 in H0; Elim (lt_n_n ? (le_lt_trans ? ? ? H H0)).
Intros; Replace (cons_Rlist l1 (cons r r0)) with (cons_Rlist (cons_Rlist l1 (cons r nil)) r0).
Inversion H0.
Rewrite <- minus_n_n; Simpl; Rewrite RList_P26.
Clear l2 r0 H i H0 H1 H2; Induction l1.
Reflexivity.
Simpl; Assumption.
Rewrite RList_P23; Rewrite plus_sym; Simpl; Apply lt_n_Sn.
Replace (minus (S m) (Rlength l1)) with (S (minus (S m) (S (Rlength l1)))).
Rewrite H3; Simpl; Replace (S (Rlength l1)) with (Rlength (cons_Rlist l1 (cons r nil))).
Apply (H (cons_Rlist l1 (cons r nil)) i).
Rewrite RList_P23; Rewrite plus_sym; Simpl; Rewrite <- H3; Apply le_n_S; Assumption.
Repeat Rewrite RList_P23; Simpl; Rewrite RList_P23 in H1; Rewrite plus_sym in H1; Simpl in H1; Rewrite (plus_sym (Rlength l1)); Simpl; Rewrite plus_sym; Apply H1.
Rewrite RList_P23; Rewrite plus_sym; Reflexivity.
Change (S (minus m (Rlength l1)))=(minus (S m) (Rlength l1)); Apply minus_Sn_m; Assumption.
Replace (cons r r0) with (cons_Rlist (cons r nil) r0); [Symmetry; Apply RList_P27 | Reflexivity].
Qed.
