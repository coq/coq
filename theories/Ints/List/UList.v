
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(***********************************************************************
      UList.v                                                                                       
                                                                                                         
      Definition of list with distinct elements                                 
                                                                                                         
      Definition: ulist                                                                         
************************************************************************)
Require Import List.
Require Import Arith.
Require Import Permutation.
Require Import ListSet.
 
Section UniqueList.
Variable A : Set.
Variable eqA_dec : forall (a b : A),  ({ a = b }) + ({ a <> b }).
(* A list is unique if there is not twice the same element in the list *)
 
Inductive ulist : list A ->  Prop :=
  ulist_nil: ulist nil
 | ulist_cons: forall a l, ~ In a l -> ulist l ->  ulist (a :: l) .
Hint Constructors ulist .
(* Inversion theorem *)
 
Theorem ulist_inv: forall a l, ulist (a :: l) ->  ulist l.
intros a l H; inversion H; auto.
Qed.
(* The append of two unique list is unique if the list are distinct *)
 
Theorem ulist_app:
 forall l1 l2,
 ulist l1 ->
 ulist l2 -> (forall (a : A), In a l1 -> In a l2 ->  False) ->  ulist (l1 ++ l2).
intros L1; elim L1; simpl; auto.
intros a l H l2 H0 H1 H2; apply ulist_cons; simpl; auto.
red; intros H3; case in_app_or with ( 1 := H3 ); auto; intros H4.
inversion H0; auto.
apply H2 with a; auto.
apply H; auto.
apply ulist_inv with ( 1 := H0 ); auto.
intros a0 H3 H4; apply (H2 a0); auto.
Qed.
(* Iinversion theorem the appended list *)
 
Theorem ulist_app_inv:
 forall l1 l2 (a : A), ulist (l1 ++ l2) -> In a l1 -> In a l2 ->  False.
intros l1; elim l1; simpl; auto.
intros a l H l2 a0 H0 [H1|H1] H2.
inversion H0 as [|a1 l0 H3 H4 H5]; auto.
case H4; rewrite H1; auto with datatypes.
apply (H l2 a0); auto.
apply ulist_inv with ( 1 := H0 ); auto.
Qed.
(* Iinversion theorem the appended list *)
 
Theorem ulist_app_inv_l: forall (l1 l2 : list A), ulist (l1 ++ l2) ->  ulist l1.
intros l1; elim l1; simpl; auto.
intros a l H l2 H0.
inversion H0 as [|il1 iH1 iH2 il2 [iH4 iH5]]; apply ulist_cons; auto.
intros H5; case iH2; auto with datatypes.
apply H with l2; auto.
Qed.
(* Iinversion theorem the appended list *)
 
Theorem ulist_app_inv_r: forall (l1 l2 : list A), ulist (l1 ++ l2) ->  ulist l2.
intros l1; elim l1; simpl; auto.
intros a l H l2 H0; inversion H0; auto.
Qed.
(* Uniqueness is decidable *)
 
Definition ulist_dec: forall l,  ({ ulist l }) + ({ ~ ulist l }).
intros l; elim l; auto.
intros a l1 [H|H]; auto.
case (In_dec eqA_dec a l1); intros H2; auto.
right; red; intros H1; inversion H1; auto.
right; intros H1; case H; apply ulist_inv with ( 1 := H1 ).
Defined.
(* Uniqueness is compatible with permutation *)
 
Theorem ulist_perm:
 forall (l1 l2 : list A), permutation l1 l2 -> ulist l1 ->  ulist l2.
intros l1 l2 H; elim H; clear H l1 l2; simpl; auto.
intros a l1 l2 H0 H1 H2; apply ulist_cons; auto.
inversion_clear H2 as [|ia il iH1 iH2 [iH3 iH4]]; auto.
intros H3; case iH1;
 apply permutation_in with ( 1 := permutation_sym _ _ _ H0 ); auto.
inversion H2; auto.
intros a b L H0; apply ulist_cons; auto.
inversion_clear H0 as [|ia il iH1 iH2]; auto.
inversion_clear iH2 as [|ia il iH3 iH4]; auto.
intros H; case H; auto.
intros H1; case iH1; rewrite H1; simpl; auto.
apply ulist_cons; auto.
inversion_clear H0 as [|ia il iH1 iH2]; auto.
intros H; case iH1; simpl; auto.
inversion_clear H0 as [|ia il iH1 iH2]; auto.
inversion iH2; auto.
Qed.
 
Theorem ulist_def:
 forall l a,
 In a l -> ulist l ->  ~ (exists l1 , permutation l (a :: (a :: l1)) ).
intros l a H H0 [l1 H1].
absurd (ulist (a :: (a :: l1))); auto.
intros H2; inversion_clear H2; simpl; auto with datatypes.
apply ulist_perm with ( 1 := H1 ); auto.
Qed.
 
Theorem ulist_incl_permutation:
 forall (l1 l2 : list A),
 ulist l1 -> incl l1 l2 ->  (exists l3 , permutation l2 (l1 ++ l3) ).
intros l1; elim l1; simpl; auto.
intros l2 H H0; exists l2; simpl; auto.
intros a l H l2 H0 H1; auto.
case (in_permutation_ex _ a l2); auto with datatypes.
intros l3 Hl3.
case (H l3); auto.
apply ulist_inv with ( 1 := H0 ); auto.
intros b Hb.
assert (H2: In b (a :: l3)).
apply permutation_in with ( 1 := permutation_sym _ _ _ Hl3 );
 auto with datatypes.
simpl in H2 |-; case H2; intros H3; simpl; auto.
inversion_clear H0 as [|c lc Hk1]; auto.
case Hk1; subst a; auto.
intros l4 H4; exists l4.
apply permutation_trans with (a :: l3); auto.
apply permutation_sym; auto.
Qed.
 
Theorem ulist_eq_permutation:
 forall (l1 l2 : list A),
 ulist l1 -> incl l1 l2 -> length l1 = length l2 ->  permutation l1 l2.
intros l1 l2 H1 H2 H3.
case (ulist_incl_permutation l1 l2); auto.
intros l3 H4.
assert (H5: l3 = @nil A).
generalize (permutation_length _ _ _ H4); rewrite length_app; rewrite H3.
rewrite plus_comm; case l3; simpl; auto.
intros a l H5; absurd (lt (length l2) (length l2)); auto with arith.
pattern (length l2) at 2; rewrite H5; auto with arith.
replace l1 with (app l1 l3); auto.
apply permutation_sym; auto.
rewrite H5; rewrite app_nil_end; auto.
Qed.
 

Theorem ulist_incl_length:
 forall (l1 l2 : list A), ulist l1 -> incl l1 l2 ->  le (length l1) (length l2).
intros l1 l2 H1 Hi; case ulist_incl_permutation with ( 2 := Hi ); auto.
intros l3 Hl3; rewrite permutation_length with ( 1 := Hl3 ); auto.
rewrite length_app; simpl; auto with arith.
Qed.

Theorem ulist_incl2_permutation:
 forall (l1 l2 : list A),
 ulist l1 -> ulist l2 -> incl l1 l2 -> incl l2 l1  ->  permutation l1 l2.
intros l1 l2 H1 H2 H3 H4.
apply ulist_eq_permutation; auto.
apply le_antisym; apply ulist_incl_length; auto.
Qed.
 
 
Theorem ulist_incl_length_strict:
 forall (l1 l2 : list A),
 ulist l1 -> incl l1 l2 -> ~ incl l2 l1 ->  lt (length l1) (length l2).
intros l1 l2 H1 Hi Hi0; case ulist_incl_permutation with ( 2 := Hi ); auto.
intros l3 Hl3; rewrite permutation_length with ( 1 := Hl3 ); auto.
rewrite length_app; simpl; auto with arith.
generalize Hl3; case l3; simpl; auto with arith.
rewrite <- app_nil_end; auto.
intros H2; case Hi0; auto.
intros a HH; apply permutation_in with ( 1 := H2 ); auto.
intros a l Hl0; (rewrite plus_comm; simpl; rewrite plus_comm; auto with arith).
Qed.
 
Theorem in_inv_dec:
 forall (a b : A) l, In a (cons b l) ->  a = b \/ ~ a = b /\ In a l.
intros a b l H; case (eqA_dec a b); auto; intros H1.
right; split; auto; inversion H; auto.
case H1; auto.
Qed.
 
Theorem in_ex_app_first:
 forall (a : A) (l : list A),
 In a l ->
  (exists l1 : list A , exists l2 : list A , l = l1 ++ (a :: l2) /\ ~ In a l1  ).
intros a l; elim l; clear l; auto.
intros H; case H.
intros a1 l H H1; auto.
generalize (in_inv_dec _ _ _ H1); intros [H2|[H2 H3]].
exists (nil (A:=A)); exists l; simpl; split; auto.
eq_tac; auto.
case H; auto; intros l1 [l2 [Hl2 Hl3]]; exists (a1 :: l1); exists l2; simpl;
 split; auto.
eq_tac; auto.
intros H4; case H4; auto.
Qed.
 
Theorem ulist_inv_ulist:
 forall (l : list A),
 ~ ulist l ->
  (exists a ,
   exists l1 ,
   exists l2 ,
   exists l3 , l = l1 ++ ((a :: l2) ++ (a :: l3)) /\ ulist (l1 ++ (a :: l2))    ).
intros l; elim l  using list_length_ind; clear l.
intros l; case l; simpl; auto; clear l.
intros Rec H0; case H0; auto.
intros a l H H0.
case (In_dec eqA_dec a l); intros H1; auto.
case in_ex_app_first with ( 1 := H1 ); intros l1 [l2 [Hl1 Hl2]]; subst l.
case (ulist_dec l1); intros H2.
exists a; exists (@nil A); exists l1; exists l2; split; auto.
simpl; apply ulist_cons; auto.
case (H l1); auto.
rewrite length_app; auto with arith.
intros b [l3 [l4 [l5 [Hl3 Hl4]]]]; subst l1.
exists b; exists (a :: l3); exists l4; exists (l5 ++ (a :: l2)); split; simpl;
 auto.
(repeat (rewrite <- ass_app; simpl)); auto.
apply ulist_cons; auto.
contradict Hl2; auto.
replace (l3 ++ (b :: (l4 ++ (b :: l5)))) with ((l3 ++ (b :: l4)) ++ (b :: l5));
 auto with datatypes.
(repeat (rewrite <- ass_app; simpl)); auto.
case (H l); auto; intros a1 [l1 [l2 [l3 [Hl3 Hl4]]]]; subst l.
exists a1; exists (a :: l1); exists l2; exists l3; split; auto.
simpl; apply ulist_cons; auto.
contradict H1.
replace (l1 ++ (a1 :: (l2 ++ (a1 :: l3))))
     with ((l1 ++ (a1 :: l2)) ++ (a1 :: l3)); auto with datatypes.
(repeat (rewrite <- ass_app; simpl)); auto.
Qed.
 
Theorem incl_length_repetition:
 forall (l1 l2 : list A),
 incl l1 l2 ->
 lt (length l2) (length l1) ->
  (exists a ,
   exists ll1 ,
   exists ll2 ,
   exists ll3 ,
   l1 = ll1 ++ ((a :: ll2) ++ (a :: ll3)) /\ ulist (ll1 ++ (a :: ll2))    ).
intros l1 l2 H H0; apply ulist_inv_ulist.
intros H1; absurd (le (length l1) (length l2)); auto with arith.
apply ulist_incl_length; auto.
Qed.
 
End UniqueList.
Implicit Arguments ulist [A].
Hint Constructors ulist .
 
Theorem ulist_map:
 forall (A B : Set) (f : A ->  B) l,
 (forall x y, (In x l) -> (In y l) ->  f x = f y ->  x = y) -> ulist l ->  ulist (map f l).
intros a b f l Hf Hl; generalize Hf; elim Hl; clear Hf;  auto.
simpl; auto.
intros a1 l1 H1 H2 H3 Hf; simpl.
apply ulist_cons; auto with datatypes.
contradict H1.
case in_map_inv with ( 1 := H1 ); auto with datatypes.
intros b1 [Hb1 Hb2].
replace a1 with b1; auto with datatypes.
Qed.
 
Theorem ulist_list_prod:
 forall (A : Set) (l1 l2 : list A),
 ulist l1 -> ulist l2 ->  ulist (list_prod l1 l2).
intros A l1 l2 Hl1 Hl2; elim Hl1; simpl; auto.
intros a l H1 H2 H3; apply ulist_app; auto.
apply ulist_map; auto.
intros x y _ _ H; inversion H; auto.
intros p Hp1 Hp2; case H1.
case in_map_inv with ( 1 := Hp1 ); intros a1 [Ha1 Ha2]; auto.
case in_list_prod_inv with ( 1 := Hp2 ); intros b1 [c1 [Hb1 [Hb2 Hb3]]]; auto.
replace a with b1; auto.
rewrite Ha2 in Hb1; injection Hb1; auto.
Qed.
