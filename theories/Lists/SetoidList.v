(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id: Lib.v,v 1.2 2006/02/26 15:59:48 letouzey Exp $ *)

Require Export List.
Require Export MoreList.
Require Export Sorting.
Require Export Setoid.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Logical relations over lists with respect to a setoid equality 
      or ordering. *) 

(** This can be seen as a complement of predicate [lelistA] and [sort] 
    found in [Sorting]. *)

Section Type_with_equality.
Variable A : Set.
Variable eqA : A -> A -> Prop. 

(** Being in a list modulo an equality relation over type [A]. *)

Inductive InA (x : A) : list A -> Prop :=
  | InA_cons_hd : forall y l, eqA x y -> InA x (y :: l)
  | InA_cons_tl : forall y l, InA x l -> InA x (y :: l).

Hint Constructors InA.

(** An alternative definition of [InA]. *)

Lemma InA_alt : forall x l, InA x l <-> exists y, eqA x y /\ In y l.
Proof. 
 induction l; intuition.
 inversion H.
 firstorder.
 inversion H1; firstorder.
 firstorder; subst; auto.
Qed.

(** A list without redundancy. *)

Inductive noredun : list A -> Prop := 
 | noredun_nil : noredun nil 
 | noredun_cons : forall x l, ~ In x l -> noredun l -> noredun (x::l). 


(** Similarly, a list without redundancy modulo the equality over [A]. *)

Inductive noredunA : list A -> Prop :=
  | noredunA_nil : noredunA nil
  | noredunA_cons : forall x l, ~ InA x l -> noredunA l -> noredunA (x::l).

Hint Constructors noredunA.


(** Results concerning lists modulo [eqA] *)

Hypothesis eqA_refl : forall x, eqA x x.
Hypothesis eqA_sym : forall x y, eqA x y -> eqA y x.
Hypothesis eqA_trans : forall x y z, eqA x y -> eqA y z -> eqA x z.

Hint Resolve eqA_refl eqA_trans.
Hint Immediate eqA_sym.

Lemma InA_eqA : forall l x y, eqA x y -> InA x l -> InA y l.
Proof. 
 intros s x y.
 do 2 rewrite InA_alt.
 intros H (z,(U,V)).  
 exists z; split; eauto.
Qed.
Hint Immediate InA_eqA.

Lemma In_InA : forall l x, In x l -> InA x l.
Proof.
 simple induction l; simpl in |- *; intuition.
 subst; auto.  
Qed.
Hint Resolve In_InA.

(** Results concerning lists modulo [eqA] and [ltA] *)

Variable ltA : A -> A -> Prop.

Hypothesis ltA_trans : forall x y z, ltA x y -> ltA y z -> ltA x z.
Hypothesis ltA_not_eqA : forall x y, ltA x y -> ~ eqA x y.
Hypothesis ltA_eqA : forall x y z, ltA x y -> eqA y z -> ltA x z.
Hypothesis eqA_ltA : forall x y z, eqA x y -> ltA y z -> ltA x z.

Hint Resolve ltA_trans.
Hint Immediate ltA_eqA eqA_ltA.

Notation InfA:=(lelistA ltA).
Notation SortA:=(sort ltA).

Lemma InfA_ltA :
 forall l x y, ltA x y -> InfA y l -> InfA x l.
Proof.
 intro s; case s; constructor; inversion_clear H0.
 eapply ltA_trans; eauto.
Qed.
 
Lemma InfA_eqA :
 forall l x y, eqA x y -> InfA y l -> InfA x l.
Proof.
 intro s; case s; constructor; inversion_clear H0; eauto.
Qed.
Hint Immediate InfA_ltA InfA_eqA. 

Lemma SortA_InfA_InA :
 forall l x a, SortA l -> InfA a l -> InA x l -> ltA a x.
Proof. 
 simple induction l.
 intros; inversion H1.
 intros.
 inversion_clear H0; inversion_clear H1; inversion_clear H2.
 eapply ltA_eqA; eauto.
 eauto.
Qed.
  
Lemma In_InfA :
 forall l x, (forall y, In y l -> ltA x y) -> InfA x l.
Proof.
 simple induction l; simpl in |- *; intros; constructor; auto.
Qed.
 
Lemma InA_InfA :
 forall l x, (forall y, InA y l -> ltA x y) -> InfA x l.
Proof.
 simple induction l; simpl in |- *; intros; constructor; auto.
Qed.

(* In fact, this may be used as an alternative definition for InfA: *)

Lemma InfA_alt : 
 forall l x, SortA l -> (InfA x l <-> (forall y, InA y l -> ltA x y)).
Proof. 
split.
intros; eapply SortA_InfA_InA; eauto.
apply InA_InfA.
Qed.

Lemma SortA_noredunA : forall l, SortA l -> noredunA l.
Proof.
 simple induction l; auto.
 intros x l' H H0.
 inversion_clear H0.
 constructor; auto.  
 intro.
 assert (ltA x x) by eapply SortA_InfA_InA; eauto.
 elim (ltA_not_eqA H3); auto.
Qed.

Lemma noredunA_app : forall l l', noredunA l -> noredunA l' -> 
  (forall x, InA x l -> InA x l' -> False) -> 
  noredunA (l++l').
Proof.
induction l; simpl; auto; intros.
inversion_clear H.
constructor.
rewrite InA_alt; intros (y,(H4,H5)).
destruct (in_app_or _ _ _ H5).
elim H2.
rewrite InA_alt.
exists y; auto.
apply (H1 a).
auto.
rewrite InA_alt.
exists y; auto.
apply IHl; auto.
intros.
apply (H1 x); auto.
Qed.


Lemma noredunA_rev : forall l, noredunA l -> noredunA (rev l).
Proof.
induction l.
simpl; auto.
simpl; intros.
inversion_clear H.
apply noredunA_app; auto.
constructor; auto.
intro H2; inversion H2.
intros x.
rewrite InA_alt.
intros (x1,(H2,H3)).
inversion_clear 1.
destruct H0.
apply InA_eqA with x1; eauto.
apply In_InA.
rewrite In_rev; auto.
inversion H4.
Qed.


Lemma InA_app : forall l1 l2 x,
 InA x (l1 ++ l2) -> InA x l1 \/ InA x l2.
Proof.
 induction l1; simpl in *; intuition.
 inversion_clear H; auto.
 elim (IHl1 l2 x H0); auto.
Qed.

 Hint Constructors lelistA sort.

Lemma InfA_app : forall l1 l2 a, InfA a l1 -> InfA a l2 -> InfA a (l1++l2).
Proof.
 induction l1; simpl; auto.
 inversion_clear 1; auto.
Qed.

Lemma SortA_app :
 forall l1 l2, SortA l1 -> SortA l2 ->
 (forall x y, InA x l1 -> InA y l2 -> ltA x y) ->
 SortA (l1 ++ l2).
Proof.
 induction l1; simpl in *; intuition.
 inversion_clear H.
 constructor; auto.
 apply InfA_app; auto.
 destruct l2; auto.
Qed.

End Type_with_equality.

Hint Constructors InA.
Hint Constructors noredunA. 
Hint Constructors sort.
Hint Constructors lelistA.
