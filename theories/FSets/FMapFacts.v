(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Finite maps library *)

(** This functor derives additional facts from [FMapInterface.S]. These
  facts are mainly the specifications of [FMapInterface.S] written using
  different styles: equivalence and boolean equalities.
*)

Require Import Bool DecidableType DecidableTypeEx OrderedType Morphisms.
Require Export FMapInterface.
Set Implicit Arguments.
Unset Strict Implicit.

Hint Extern 1 (Equivalence _) => constructor; congruence.

(** * Facts about weak maps *)

Module WFacts_fun (E:DecidableType)(Import M:WSfun E).

Notation option_map := option_map (compat "8.7").

Notation eq_dec := E.eq_dec.
Definition eqb x y := if eq_dec x y then true else false.

Lemma eq_bool_alt : forall b b', b=b' <-> (b=true <-> b'=true).
Proof.
 destruct b; destruct b'; intuition.
Qed.

Lemma eq_option_alt : forall (elt:Type)(o o':option elt),
 o=o' <-> (forall e, o=Some e <-> o'=Some e).
Proof.
split; intros.
subst; split; auto.
destruct o; destruct o'; try rewrite H; auto.
symmetry; rewrite <- H; auto.
Qed.

Lemma MapsTo_fun : forall (elt:Type) m x (e e':elt),
  MapsTo x e m -> MapsTo x e' m -> e=e'.
Proof.
intros.
generalize (find_1 H) (find_1 H0); clear H H0.
intros; rewrite H in H0; injection H0; auto.
Qed.

(** ** Specifications written using equivalences *)

Section IffSpec.
Variable elt elt' elt'': Type.
Implicit Type m: t elt.
Implicit Type x y z: key.
Implicit Type e: elt.

Lemma In_iff : forall m x y, E.eq x y -> (In x m <-> In y m).
Proof.
unfold In.
split; intros (e0,H0); exists e0.
apply (MapsTo_1 H H0); auto.
apply (MapsTo_1 (E.eq_sym H) H0); auto.
Qed.

Lemma MapsTo_iff : forall m x y e, E.eq x y -> (MapsTo x e m <-> MapsTo y e m).
Proof.
split; apply MapsTo_1; auto.
Qed.

Lemma mem_in_iff : forall m x, In x m <-> mem x m = true.
Proof.
split; [apply mem_1|apply mem_2].
Qed.

Lemma not_mem_in_iff : forall m x, ~In x m <-> mem x m = false.
Proof.
intros; rewrite mem_in_iff; destruct (mem x m); intuition.
Qed.

Lemma In_dec : forall m x, { In x m } + { ~ In x m }.
Proof.
 intros.
 generalize (mem_in_iff m x).
 destruct (mem x m); [left|right]; intuition.
Qed.

Lemma find_mapsto_iff : forall m x e, MapsTo x e m <-> find x m = Some e.
Proof.
split; [apply find_1|apply find_2].
Qed.

Lemma not_find_in_iff : forall m x, ~In x m <-> find x m = None.
Proof.
split; intros.
rewrite eq_option_alt. intro e. rewrite <- find_mapsto_iff.
split; try discriminate. intro H'; elim H; exists e; auto.
intros (e,He); rewrite find_mapsto_iff,H in He; discriminate.
Qed.

Lemma in_find_iff : forall m x, In x m <-> find x m <> None.
Proof.
intros; rewrite <- not_find_in_iff, mem_in_iff.
destruct mem; intuition.
Qed.

Lemma equal_iff : forall m m' cmp, Equivb cmp m m' <-> equal cmp m m' = true.
Proof.
split; [apply equal_1|apply equal_2].
Qed.

Lemma empty_mapsto_iff : forall x e, MapsTo x e (empty elt) <-> False.
Proof.
intuition; apply (empty_1 H).
Qed.

Lemma empty_in_iff : forall x, In x (empty elt) <-> False.
Proof.
unfold In.
split; [intros (e,H); rewrite empty_mapsto_iff in H|]; intuition.
Qed.

Lemma is_empty_iff : forall m, Empty m <-> is_empty m = true.
Proof.
split; [apply is_empty_1|apply is_empty_2].
Qed.

Lemma add_mapsto_iff : forall m x y e e',
  MapsTo y e' (add x e m) <->
     (E.eq x y /\ e=e') \/
     (~E.eq x y /\ MapsTo y e' m).
Proof.
intros.
intuition.
destruct (eq_dec x y); [left|right].
split; auto.
symmetry; apply (MapsTo_fun (e':=e) H); auto with map.
split; auto; apply add_3 with x e; auto.
subst; auto with map.
Qed.

Lemma add_in_iff : forall m x y e, In y (add x e m) <-> E.eq x y \/ In y m.
Proof.
unfold In; split.
intros (e',H).
destruct (eq_dec x y) as [E|E]; auto.
right; exists e'; auto.
apply (add_3 E H).
destruct (eq_dec x y) as [E|E]; auto.
intros.
exists e; apply add_1; auto.
intros [H|(e',H)].
destruct E; auto.
exists e'; apply add_2; auto.
Qed.

Lemma add_neq_mapsto_iff : forall m x y e e',
 ~ E.eq x y -> (MapsTo y e' (add x e m)  <-> MapsTo y e' m).
Proof.
split; [apply add_3|apply add_2]; auto.
Qed.

Lemma add_neq_in_iff : forall m x y e,
 ~ E.eq x y -> (In y (add x e m)  <-> In y m).
Proof.
split; intros (e',H0); exists e'.
apply (add_3 H H0).
apply add_2; auto.
Qed.

Lemma remove_mapsto_iff : forall m x y e,
  MapsTo y e (remove x m) <-> ~E.eq x y /\ MapsTo y e m.
Proof.
intros.
split; intros.
split.
assert (In y (remove x m)) by (exists e; auto).
intro H1; apply (remove_1 H1 H0).
apply remove_3 with x; auto.
apply remove_2; intuition.
Qed.

Lemma remove_in_iff : forall m x y, In y (remove x m) <-> ~E.eq x y /\ In y m.
Proof.
unfold In; split.
intros (e,H).
split.
assert (In y (remove x m)) by (exists e; auto).
intro H1; apply (remove_1 H1 H0).
exists e; apply remove_3 with x; auto.
intros (H,(e,H0)); exists e; apply remove_2; auto.
Qed.

Lemma remove_neq_mapsto_iff : forall m x y e,
 ~ E.eq x y -> (MapsTo y e (remove x m)  <-> MapsTo y e m).
Proof.
split; [apply remove_3|apply remove_2]; auto.
Qed.

Lemma remove_neq_in_iff : forall m x y,
 ~ E.eq x y -> (In y (remove x m)  <-> In y m).
Proof.
split; intros (e',H0); exists e'.
apply (remove_3 H0).
apply remove_2; auto.
Qed.

Lemma elements_mapsto_iff : forall m x e,
 MapsTo x e m <-> InA (@eq_key_elt _) (x,e) (elements m).
Proof.
split; [apply elements_1 | apply elements_2].
Qed.

Lemma elements_in_iff : forall m x,
 In x m <-> exists e, InA (@eq_key_elt _) (x,e) (elements m).
Proof.
unfold In; split; intros (e,H); exists e; [apply elements_1 | apply elements_2]; auto.
Qed.

Lemma map_mapsto_iff : forall m x b (f : elt -> elt'),
 MapsTo x b (map f m) <-> exists a, b = f a /\ MapsTo x a m.
Proof.
split.
case_eq (find x m); intros.
exists e.
split.
apply (MapsTo_fun (m:=map f m) (x:=x)); auto with map.
apply find_2; auto with map.
assert (In x (map f m)) by (exists b; auto).
destruct (map_2 H1) as (a,H2).
rewrite (find_1 H2) in H; discriminate.
intros (a,(H,H0)).
subst b; auto with map.
Qed.

Lemma map_in_iff : forall m x (f : elt -> elt'),
 In x (map f m) <-> In x m.
Proof.
split; intros; eauto with map.
destruct H as (a,H).
exists (f a); auto with map.
Qed.

Lemma mapi_in_iff : forall m x (f:key->elt->elt'),
 In x (mapi f m) <-> In x m.
Proof.
split; intros; eauto with map.
destruct H as (a,H).
destruct (mapi_1 f H) as (y,(H0,H1)).
exists (f y a); auto.
Qed.

(** Unfortunately, we don't have simple equivalences for [mapi]
  and [MapsTo]. The only correct one needs compatibility of [f]. *)

Lemma mapi_inv : forall m x b (f : key -> elt -> elt'),
 MapsTo x b (mapi f m) ->
 exists a y, E.eq y x /\ b = f y a /\ MapsTo x a m.
Proof.
intros; case_eq (find x m); intros.
exists e.
destruct (@mapi_1 _ _ m x e f) as (y,(H1,H2)).
apply find_2; auto with map.
exists y; repeat split; auto with map.
apply (MapsTo_fun (m:=mapi f m) (x:=x)); auto with map.
assert (In x (mapi f m)) by (exists b; auto).
destruct (mapi_2 H1) as (a,H2).
rewrite (find_1 H2) in H0; discriminate.
Qed.

Lemma mapi_1bis : forall m x e (f:key->elt->elt'),
 (forall x y e, E.eq x y -> f x e = f y e) ->
 MapsTo x e m -> MapsTo x (f x e) (mapi f m).
Proof.
intros.
destruct (mapi_1 f H0) as (y,(H1,H2)).
replace (f x e) with (f y e) by auto.
auto.
Qed.

Lemma mapi_mapsto_iff : forall m x b (f:key->elt->elt'),
 (forall x y e, E.eq x y -> f x e = f y e) ->
 (MapsTo x b (mapi f m) <-> exists a, b = f x a /\ MapsTo x a m).
Proof.
split.
intros.
destruct (mapi_inv H0) as (a,(y,(H1,(H2,H3)))).
exists a; split; auto.
subst b; auto.
intros (a,(H0,H1)).
subst b.
apply mapi_1bis; auto.
Qed.

(** Things are even worse for [map2] : we don't try to state any
 equivalence, see instead boolean results below. *)

End IffSpec.

(** Useful tactic for simplifying expressions like [In y (add x e (remove z m))] *)

Ltac map_iff :=
 repeat (progress (
  rewrite add_mapsto_iff || rewrite add_in_iff ||
  rewrite remove_mapsto_iff || rewrite remove_in_iff ||
  rewrite empty_mapsto_iff || rewrite empty_in_iff ||
  rewrite map_mapsto_iff || rewrite map_in_iff ||
  rewrite mapi_in_iff)).

(** ** Specifications written using boolean predicates *)

Section BoolSpec.

Lemma mem_find_b : forall (elt:Type)(m:t elt)(x:key), mem x m = if find x m then true else false.
Proof.
intros.
generalize (find_mapsto_iff m x)(mem_in_iff m x); unfold In.
destruct (find x m); destruct (mem x m); auto.
intros.
rewrite <- H0; exists e; rewrite H; auto.
intuition.
destruct H0 as (e,H0).
destruct (H e); intuition discriminate.
Qed.

Variable elt elt' elt'' : Type.
Implicit Types m : t elt.
Implicit Types x y z : key.
Implicit Types e : elt.

Lemma mem_b : forall m x y, E.eq x y -> mem x m = mem y m.
Proof.
intros.
generalize (mem_in_iff m x) (mem_in_iff m y)(In_iff m H).
destruct (mem x m); destruct (mem y m); intuition.
Qed.

Lemma find_o : forall m x y, E.eq x y -> find x m = find y m.
Proof.
intros. rewrite eq_option_alt. intro e. rewrite <- 2 find_mapsto_iff.
apply MapsTo_iff; auto.
Qed.

Lemma empty_o : forall x, find x (empty elt) = None.
Proof.
intros. rewrite eq_option_alt. intro e.
rewrite <- find_mapsto_iff, empty_mapsto_iff; now intuition.
Qed.

Lemma empty_a : forall x, mem x (empty elt) = false.
Proof.
intros.
case_eq (mem x (empty elt)); intros; auto.
generalize (mem_2 H).
rewrite empty_in_iff; intuition.
Qed.

Lemma add_eq_o : forall m x y e,
 E.eq x y -> find y (add x e m) = Some e.
Proof.
auto with map.
Qed.

Lemma add_neq_o : forall m x y e,
 ~ E.eq x y -> find y (add x e m) = find y m.
Proof.
intros. rewrite eq_option_alt. intro e'. rewrite <- 2 find_mapsto_iff.
apply add_neq_mapsto_iff; auto.
Qed.
Hint Resolve add_neq_o : map.

Lemma add_o : forall m x y e,
 find y (add x e m) = if eq_dec x y then Some e else find y m.
Proof.
intros; destruct (eq_dec x y); auto with map.
Qed.

Lemma add_eq_b : forall m x y e,
 E.eq x y -> mem y (add x e m) = true.
Proof.
intros; rewrite mem_find_b; rewrite add_eq_o; auto.
Qed.

Lemma add_neq_b : forall m x y e,
 ~E.eq x y -> mem y (add x e m) = mem y m.
Proof.
intros; do 2 rewrite mem_find_b; rewrite add_neq_o; auto.
Qed.

Lemma add_b : forall m x y e,
 mem y (add x e m) = eqb x y || mem y m.
Proof.
intros; do 2 rewrite mem_find_b; rewrite add_o; unfold eqb.
destruct (eq_dec x y); simpl; auto.
Qed.

Lemma remove_eq_o : forall m x y,
 E.eq x y -> find y (remove x m) = None.
Proof.
intros. rewrite eq_option_alt. intro e.
rewrite <- find_mapsto_iff, remove_mapsto_iff; now intuition.
Qed.
Hint Resolve remove_eq_o : map.

Lemma remove_neq_o : forall m x y,
 ~ E.eq x y -> find y (remove x m) = find y m.
Proof.
intros. rewrite eq_option_alt. intro e.
rewrite <- find_mapsto_iff, remove_neq_mapsto_iff; now intuition.
Qed.
Hint Resolve remove_neq_o : map.

Lemma remove_o : forall m x y,
 find y (remove x m) = if eq_dec x y then None else find y m.
Proof.
intros; destruct (eq_dec x y); auto with map.
Qed.

Lemma remove_eq_b : forall m x y,
 E.eq x y -> mem y (remove x m) = false.
Proof.
intros; rewrite mem_find_b; rewrite remove_eq_o; auto.
Qed.

Lemma remove_neq_b : forall m x y,
 ~ E.eq x y -> mem y (remove x m) = mem y m.
Proof.
intros; do 2 rewrite mem_find_b; rewrite remove_neq_o; auto.
Qed.

Lemma remove_b : forall m x y,
 mem y (remove x m) = negb (eqb x y) && mem y m.
Proof.
intros; do 2 rewrite mem_find_b; rewrite remove_o; unfold eqb.
destruct (eq_dec x y); auto.
Qed.

Lemma map_o : forall m x (f:elt->elt'),
 find x (map f m) = Datatypes.option_map f (find x m).
Proof.
intros.
generalize (find_mapsto_iff (map f m) x) (find_mapsto_iff m x)
  (fun b => map_mapsto_iff m x b f).
destruct (find x (map f m)); destruct (find x m); simpl; auto; intros.
rewrite <- H; rewrite H1; exists e0; rewrite H0; auto.
destruct (H e) as [_ H2].
rewrite H1 in H2.
destruct H2 as (a,(_,H2)); auto.
rewrite H0 in H2; discriminate.
rewrite <- H; rewrite H1; exists e; rewrite H0; auto.
Qed.

Lemma map_b : forall m x (f:elt->elt'),
 mem x (map f m) = mem x m.
Proof.
intros; do 2 rewrite mem_find_b; rewrite map_o.
destruct (find x m); simpl; auto.
Qed.

Lemma mapi_b : forall m x (f:key->elt->elt'),
 mem x (mapi f m) = mem x m.
Proof.
intros.
generalize (mem_in_iff (mapi f m) x) (mem_in_iff m x) (mapi_in_iff m x f).
destruct (mem x (mapi f m)); destruct (mem x m); simpl; auto; intros.
symmetry; rewrite <- H0; rewrite <- H1; rewrite H; auto.
rewrite <- H; rewrite H1; rewrite H0; auto.
Qed.

Lemma mapi_o : forall m x (f:key->elt->elt'),
 (forall x y e, E.eq x y -> f x e = f y e) ->
 find x (mapi f m) = Datatypes.option_map (f x) (find x m).
Proof.
intros.
generalize (find_mapsto_iff (mapi f m) x) (find_mapsto_iff m x)
  (fun b => mapi_mapsto_iff m x b H).
destruct (find x (mapi f m)); destruct (find x m); simpl; auto; intros.
rewrite <- H0; rewrite H2; exists e0; rewrite H1; auto.
destruct (H0 e) as [_ H3].
rewrite H2 in H3.
destruct H3 as (a,(_,H3)); auto.
rewrite H1 in H3; discriminate.
rewrite <- H0; rewrite H2; exists e; rewrite H1; auto.
Qed.

Lemma map2_1bis : forall (m: t elt)(m': t elt') x
 (f:option elt->option elt'->option elt''),
 f None None = None ->
 find x (map2 f m m') = f (find x m) (find x m').
Proof.
intros.
case_eq (find x m); intros.
rewrite <- H0.
apply map2_1; auto with map.
left; exists e; auto with map.
case_eq (find x m'); intros.
rewrite <- H0; rewrite <- H1.
apply map2_1; auto.
right; exists e; auto with map.
rewrite H.
case_eq (find x (map2 f m m')); intros; auto with map.
assert (In x (map2 f m m')) by (exists e; auto with map).
destruct (map2_2 H3) as [(e0,H4)|(e0,H4)].
rewrite (find_1 H4) in H0; discriminate.
rewrite (find_1 H4) in H1; discriminate.
Qed.

Lemma elements_o : forall m x,
 find x m = findA (eqb x) (elements m).
Proof.
intros. rewrite eq_option_alt. intro e.
rewrite <- find_mapsto_iff, elements_mapsto_iff.
unfold eqb.
rewrite <- findA_NoDupA; dintuition; try apply elements_3w; eauto.
Qed.

Lemma elements_b : forall m x,
 mem x m = existsb (fun p => eqb x (fst p)) (elements m).
Proof.
intros.
generalize (mem_in_iff m x)(elements_in_iff m x)
 (existsb_exists (fun p => eqb x (fst p)) (elements m)).
destruct (mem x m); destruct (existsb (fun p => eqb x (fst p)) (elements m)); auto; intros.
symmetry; rewrite H1.
destruct H0 as (H0,_).
destruct H0 as (e,He); [ intuition |].
rewrite InA_alt in He.
destruct He as ((y,e'),(Ha1,Ha2)).
compute in Ha1; destruct Ha1; subst e'.
exists (y,e); split; simpl; auto.
unfold eqb; destruct (eq_dec x y); intuition.
rewrite <- H; rewrite H0.
destruct H1 as (H1,_).
destruct H1 as ((y,e),(Ha1,Ha2)); [intuition|].
simpl in Ha2.
unfold eqb in *; destruct (eq_dec x y); auto; try discriminate.
exists e; rewrite InA_alt.
exists (y,e); intuition.
compute; auto.
Qed.

End BoolSpec.

Section Equalities.

Variable elt:Type.

 (** Another characterisation of [Equal] *)

Lemma Equal_mapsto_iff : forall m1 m2 : t elt,
 Equal m1 m2 <-> (forall k e, MapsTo k e m1 <-> MapsTo k e m2).
Proof.
intros m1 m2. split; [intros Heq k e|intros Hiff].
rewrite 2 find_mapsto_iff, Heq. split; auto.
intro k. rewrite eq_option_alt. intro e.
rewrite <- 2 find_mapsto_iff; auto.
Qed.

(** * Relations between [Equal], [Equiv] and [Equivb]. *)

(** First, [Equal] is [Equiv] with Leibniz on elements. *)

Lemma Equal_Equiv : forall (m m' : t elt),
  Equal m m' <-> Equiv Logic.eq m m'.
Proof.
intros. rewrite Equal_mapsto_iff. split; intros.
split.
split; intros (e,Hin); exists e; [rewrite <- H|rewrite H]; auto.
intros; apply MapsTo_fun with m k; auto; rewrite H; auto.
split; intros H'.
destruct H.
assert (Hin : In k m') by (rewrite <- H; exists e; auto).
destruct Hin as (e',He').
rewrite (H0 k e e'); auto.
destruct H.
assert (Hin : In k m) by (rewrite H; exists e; auto).
destruct Hin as (e',He').
rewrite <- (H0 k e' e); auto.
Qed.

(** [Equivb] and [Equiv] and equivalent when [eq_elt] and [cmp]
    are related. *)

Section Cmp.
Variable eq_elt : elt->elt->Prop.
Variable cmp : elt->elt->bool.

Definition compat_cmp :=
 forall e e', cmp e e' = true <-> eq_elt e e'.

Lemma Equiv_Equivb : compat_cmp ->
 forall m m', Equiv eq_elt m m' <-> Equivb cmp m m'.
Proof.
 unfold Equivb, Equiv, Cmp; intuition.
 red in H; rewrite H; eauto.
 red in H; rewrite <-H; eauto.
Qed.
End Cmp.

(** Composition of the two last results: relation between [Equal]
    and [Equivb]. *)

Lemma Equal_Equivb : forall cmp,
 (forall e e', cmp e e' = true <-> e = e') ->
 forall (m m':t elt), Equal m m' <-> Equivb cmp m m'.
Proof.
 intros; rewrite Equal_Equiv.
 apply Equiv_Equivb; auto.
Qed.

Lemma Equal_Equivb_eqdec :
 forall eq_elt_dec : (forall e e', { e = e' } + { e <> e' }),
 let cmp := fun e e' => if eq_elt_dec e e' then true else false in
 forall (m m':t elt), Equal m m' <-> Equivb cmp m m'.
Proof.
intros; apply Equal_Equivb.
unfold cmp; clear cmp; intros.
destruct eq_elt_dec; now intuition.
Qed.

End Equalities.

(** * [Equal] is a setoid equality. *)

Lemma Equal_refl : forall (elt:Type)(m : t elt), Equal m m.
Proof. red; reflexivity. Qed.

Lemma Equal_sym : forall (elt:Type)(m m' : t elt),
 Equal m m' -> Equal m' m.
Proof. unfold Equal; auto. Qed.

Lemma Equal_trans : forall (elt:Type)(m m' m'' : t elt),
 Equal m m' -> Equal m' m'' -> Equal m m''.
Proof. unfold Equal; congruence. Qed.

Definition Equal_ST : forall elt:Type, Equivalence (@Equal elt).
Proof.
constructor; red; [apply Equal_refl | apply Equal_sym | apply Equal_trans].
Qed.

Add Relation key E.eq
 reflexivity proved by E.eq_refl
 symmetry proved by E.eq_sym
 transitivity proved by E.eq_trans
 as KeySetoid.

Arguments Equal {elt} m m'.

Add Parametric Relation (elt : Type) : (t elt) Equal
 reflexivity proved by (@Equal_refl elt)
 symmetry proved by (@Equal_sym elt)
 transitivity proved by (@Equal_trans elt)
 as EqualSetoid.

Add Parametric Morphism elt : (@In elt)
 with signature E.eq ==> Equal ==> iff as In_m.
Proof.
unfold Equal; intros k k' Hk m m' Hm.
rewrite (In_iff m Hk), in_find_iff, in_find_iff, Hm; intuition.
Qed.

Add Parametric Morphism elt : (@MapsTo elt)
 with signature E.eq ==> eq ==> Equal ==> iff as MapsTo_m.
Proof.
unfold Equal; intros k k' Hk e m m' Hm.
rewrite (MapsTo_iff m e Hk), find_mapsto_iff, find_mapsto_iff, Hm;
 intuition.
Qed.

Add Parametric Morphism elt : (@Empty elt)
 with signature Equal ==> iff as Empty_m.
Proof.
unfold Empty; intros m m' Hm. split; intros; intro. 
rewrite <-Hm in H0; eapply H, H0.
rewrite Hm in H0; eapply H, H0.
Qed.

Add Parametric Morphism elt : (@is_empty elt)
 with signature Equal ==> eq as is_empty_m.
Proof.
intros m m' Hm.
rewrite eq_bool_alt, <-is_empty_iff, <-is_empty_iff, Hm; intuition.
Qed.

Add Parametric Morphism elt : (@mem elt)
 with signature E.eq ==> Equal ==> eq as mem_m.
Proof.
intros k k' Hk m m' Hm.
rewrite eq_bool_alt, <- mem_in_iff, <-mem_in_iff, Hk, Hm; intuition.
Qed.

Add Parametric Morphism elt : (@find elt)
 with signature E.eq ==> Equal ==> eq as find_m.
Proof.
intros k k' Hk m m' Hm. rewrite eq_option_alt. intro e.
rewrite <- 2 find_mapsto_iff, Hk, Hm. split; auto.
Qed.

Add Parametric Morphism elt : (@add elt)
 with signature E.eq ==> eq ==> Equal ==> Equal as add_m.
Proof.
intros k k' Hk e m m' Hm y.
rewrite add_o, add_o; do 2 destruct eq_dec as [|?Hnot]; auto.
elim Hnot; rewrite <-Hk; auto.
elim Hnot; rewrite Hk; auto.
Qed.

Add Parametric Morphism elt : (@remove elt)
 with signature E.eq ==> Equal ==> Equal as remove_m.
Proof.
intros k k' Hk m m' Hm y.
rewrite remove_o, remove_o; do 2 destruct eq_dec as [|?Hnot]; auto.
elim Hnot; rewrite <-Hk; auto.
elim Hnot; rewrite Hk; auto.
Qed.

Add Parametric Morphism elt elt' : (@map elt elt')
 with signature eq ==> Equal ==> Equal as map_m.
Proof.
intros f m m' Hm y.
rewrite map_o, map_o, Hm; auto.
Qed.

(* Later: Add Morphism cardinal *)

(* old name: *)
Notation not_find_mapsto_iff := not_find_in_iff.

End WFacts_fun.

(** * Same facts for self-contained weak sets and for full maps *)

Module WFacts (M:WS) := WFacts_fun M.E M.
Module Facts := WFacts.

(** * Additional Properties for weak maps

    Results about [fold], [elements], induction principles...
*)

Module WProperties_fun (E:DecidableType)(M:WSfun E).
 Module Import F:=WFacts_fun E M.
 Import M.

 Section Elt.
  Variable elt:Type.

  Definition Add x (e:elt) m m' := forall y, find y m' = find y (add x e m).

  Notation eqke := (@eq_key_elt elt).
  Notation eqk := (@eq_key elt).

  Instance eqk_equiv : Equivalence eqk.
  Proof. unfold eq_key; split; eauto. Qed.
  
  Instance eqke_equiv : Equivalence eqke.
  Proof.
   unfold eq_key_elt; split; repeat red; firstorder.
   eauto with *.
   congruence.
  Qed.

  (** Complements about InA, NoDupA and findA *)

  Lemma InA_eqke_eqk : forall k1 k2 e1 e2 l,
    E.eq k1 k2 -> InA eqke (k1,e1) l -> InA eqk (k2,e2) l.
  Proof.
  intros k1 k2 e1 e2 l Hk. rewrite 2 InA_alt.
  intros ((k',e') & (Hk',He') & H); simpl in *.
  exists (k',e'); split; auto.
  red; simpl; eauto.
  Qed.

  Lemma NoDupA_eqk_eqke : forall l, NoDupA eqk l -> NoDupA eqke l.
  Proof.
  induction 1; auto.
  constructor; auto.
  destruct x as (k,e).
  eauto using InA_eqke_eqk.
  Qed.

  Lemma findA_rev : forall l k, NoDupA eqk l ->
    findA (eqb k) l = findA (eqb k) (rev l).
  Proof.
  intros.
  case_eq (findA (eqb k) l).
  intros. symmetry.
  unfold eqb.
  rewrite <- findA_NoDupA, InA_rev, findA_NoDupA
   by (eauto using NoDupA_rev with *); eauto.
  case_eq (findA (eqb k) (rev l)); auto.
  intros e.
  unfold eqb.
  rewrite <- findA_NoDupA, InA_rev, findA_NoDupA
   by (eauto using NoDupA_rev with *).
  intro Eq; rewrite Eq; auto.
  Qed.

  (** * Elements *)

  Lemma elements_Empty : forall m:t elt, Empty m <-> elements m = nil.
  Proof.
  intros.
  unfold Empty.
  split; intros.
  assert (forall a, ~ List.In a (elements m)).
   red; intros.
   apply (H (fst a) (snd a)).
   rewrite elements_mapsto_iff.
   rewrite InA_alt; exists a; auto.
   split; auto; split; auto.
  destruct (elements m); auto.
  elim (H0 p); simpl; auto.
  red; intros.
  rewrite elements_mapsto_iff in H0.
  rewrite InA_alt in H0; destruct H0.
  rewrite H in H0; destruct H0 as (_,H0); inversion H0.
  Qed.

  Lemma elements_empty : elements (@empty elt) = nil.
  Proof.
  rewrite <-elements_Empty; apply empty_1.
  Qed.

  (** * Conversions between maps and association lists. *)

  Definition uncurry {U V W : Type} (f : U -> V -> W) : U*V -> W :=
   fun p => f (fst p) (snd p).

  Definition of_list :=
    List.fold_right (uncurry (@add _)) (empty elt).

  Definition to_list := elements.

  Lemma of_list_1 : forall l k e,
    NoDupA eqk l ->
    (MapsTo k e (of_list l) <-> InA eqke (k,e) l).
  Proof.
  induction l as [|(k',e') l IH]; simpl; intros k e Hnodup.
  rewrite empty_mapsto_iff, InA_nil; intuition.
  unfold uncurry; simpl.
  inversion_clear Hnodup as [| ? ? Hnotin Hnodup'].
  specialize (IH k e Hnodup'); clear Hnodup'.
  rewrite add_mapsto_iff, InA_cons, <- IH.
  unfold eq_key_elt at 1; simpl.
  split; destruct 1 as [H|H]; try (intuition;fail).
  destruct (eq_dec k k'); [left|right]; split; auto.
  contradict Hnotin.
  apply InA_eqke_eqk with k e; intuition.
  Qed.

  Lemma of_list_1b : forall l k,
    NoDupA eqk l ->
    find k (of_list l) = findA (eqb k) l.
  Proof.
  induction l as [|(k',e') l IH]; simpl; intros k Hnodup.
  apply empty_o.
  unfold uncurry; simpl.
  inversion_clear Hnodup as [| ? ? Hnotin Hnodup'].
  specialize (IH k Hnodup'); clear Hnodup'.
  rewrite add_o, IH.
  unfold eqb; do 2 destruct eq_dec as [|?Hnot]; auto; elim Hnot; eauto.
  Qed.

  Lemma of_list_2 : forall l, NoDupA eqk l ->
    equivlistA eqke l (to_list (of_list l)).
  Proof.
  intros l Hnodup (k,e).
  rewrite <- elements_mapsto_iff, of_list_1; intuition.
  Qed.

  Lemma of_list_3 : forall s, Equal (of_list (to_list s)) s.
  Proof.
  intros s k.
  rewrite of_list_1b, elements_o; auto.
  apply elements_3w.
  Qed.

  (** * Fold *)

  (** Alternative specification via [fold_right] *)

  Lemma fold_spec_right m (A:Type)(i:A)(f : key -> elt -> A -> A) :
    fold f m i = List.fold_right (uncurry f) i (rev (elements m)).
  Proof.
   rewrite fold_1. symmetry. apply fold_left_rev_right.
  Qed.

  (** ** Induction principles about fold contributed by S. Lescuyer *)

  (** In the following lemma, the step hypothesis is deliberately restricted
      to the precise map m we are considering. *)

  Lemma fold_rec :
    forall (A:Type)(P : t elt -> A -> Type)(f : key -> elt -> A -> A),
     forall (i:A)(m:t elt),
      (forall m, Empty m -> P m i) ->
      (forall k e a m' m'', MapsTo k e m -> ~In k m' ->
         Add k e m' m'' -> P m' a -> P m'' (f k e a)) ->
      P m (fold f m i).
  Proof.
  intros A P f i m Hempty Hstep.
  rewrite fold_spec_right.
  set (F:=uncurry f).
  set (l:=rev (elements m)).
  assert (Hstep' : forall k e a m' m'', InA eqke (k,e) l -> ~In k m' ->
             Add k e m' m'' -> P m' a -> P m'' (F (k,e) a)).
   intros k e a m' m'' H ? ? ?; eapply Hstep; eauto.
   revert H; unfold l; rewrite InA_rev, elements_mapsto_iff; auto with *.
  assert (Hdup : NoDupA eqk l).
   unfold l. apply NoDupA_rev; try red; unfold eq_key ; eauto with *.
   apply elements_3w.
  assert (Hsame : forall k, find k m = findA (eqb k) l).
   intros k. unfold l. rewrite elements_o, findA_rev; auto.
   apply elements_3w.
  clearbody l. clearbody F. clear Hstep f. revert m Hsame. induction l.
  (* empty *)
  intros m Hsame; simpl.
  apply Hempty. intros k e.
  rewrite find_mapsto_iff, Hsame; simpl; discriminate.
  (* step *)
  intros m Hsame; destruct a as (k,e); simpl.
  apply Hstep' with (of_list l); auto.
   rewrite InA_cons; left; red; auto.
   inversion_clear Hdup. contradict H. destruct H as (e',He').
   apply InA_eqke_eqk with k e'; auto.
   rewrite <- of_list_1; auto.
   intro k'. rewrite Hsame, add_o, of_list_1b. simpl.
   unfold eqb. do 2 destruct eq_dec as [|?Hnot]; auto; elim Hnot; eauto.
   inversion_clear Hdup; auto.
  apply IHl.
   intros; eapply Hstep'; eauto.
   inversion_clear Hdup; auto.
   intros; apply of_list_1b. inversion_clear Hdup; auto.
  Qed.

  (** Same, with [empty] and [add] instead of [Empty] and [Add]. In this
      case, [P] must be compatible with equality of sets *)

  Theorem fold_rec_bis :
    forall (A:Type)(P : t elt -> A -> Type)(f : key -> elt -> A -> A),
     forall (i:A)(m:t elt),
     (forall m m' a, Equal m m' -> P m a -> P m' a) ->
     (P (empty _) i) ->
     (forall k e a m', MapsTo k e m -> ~In k m' ->
       P m' a -> P (add k e m') (f k e a)) ->
     P m (fold f m i).
  Proof.
  intros A P f i m Pmorphism Pempty Pstep.
  apply fold_rec; intros.
  apply Pmorphism with (empty _); auto. intro k. rewrite empty_o.
  case_eq (find k m0); auto; intros e'; rewrite <- find_mapsto_iff.
  intro H'; elim (H k e'); auto.
  apply Pmorphism with (add k e m'); try intro; auto.
  Qed.

  Lemma fold_rec_nodep :
    forall (A:Type)(P : A -> Type)(f : key -> elt -> A -> A)(i:A)(m:t elt),
     P i -> (forall k e a, MapsTo k e m -> P a -> P (f k e a)) ->
     P (fold f m i).
  Proof.
  intros; apply fold_rec_bis with (P:=fun _ => P); auto.
  Qed.

  (** [fold_rec_weak] is a weaker principle than [fold_rec_bis] :
      the step hypothesis must here be applicable anywhere.
      At the same time, it looks more like an induction principle,
      and hence can be easier to use. *)

  Lemma fold_rec_weak :
    forall (A:Type)(P : t elt -> A -> Type)(f : key -> elt -> A -> A)(i:A),
    (forall m m' a, Equal m m' -> P m a -> P m' a) ->
    P (empty _) i ->
    (forall k e a m, ~In k m -> P m a -> P (add k e m) (f k e a)) ->
    forall m, P m (fold f m i).
  Proof.
  intros; apply fold_rec_bis; auto.
  Qed.

  Lemma fold_rel :
    forall (A B:Type)(R : A -> B -> Type)
     (f : key -> elt -> A -> A)(g : key -> elt -> B -> B)(i : A)(j : B)
     (m : t elt),
     R i j ->
     (forall k e a b, MapsTo k e m -> R a b -> R (f k e a) (g k e b)) ->
     R (fold f m i) (fold g m j).
  Proof.
  intros A B R f g i j m Rempty Rstep.
  rewrite 2 fold_spec_right. set (l:=rev (elements m)).
  assert (Rstep' : forall k e a b, InA eqke (k,e) l ->
    R a b -> R (f k e a) (g k e b)) by
    (intros; apply Rstep; auto; rewrite elements_mapsto_iff, <- InA_rev; auto with *).
  clearbody l; clear Rstep m.
  induction l; simpl; auto.
  apply Rstep'; auto.
  destruct a; simpl; rewrite InA_cons; left; red; auto.
  Qed.

  (** From the induction principle on [fold], we can deduce some general
      induction principles on maps. *)

  Lemma map_induction :
   forall P : t elt -> Type,
   (forall m, Empty m -> P m) ->
   (forall m m', P m -> forall x e, ~In x m -> Add x e m m' -> P m') ->
   forall m, P m.
  Proof.
  intros. apply (@fold_rec _ (fun s _ => P s) (fun _ _ _ => tt) tt m); eauto.
  Qed.

  Lemma map_induction_bis :
   forall P : t elt -> Type,
   (forall m m', Equal m m' -> P m -> P m') ->
   P (empty _) ->
   (forall x e m, ~In x m -> P m -> P (add x e m)) ->
   forall m, P m.
  Proof.
  intros.
  apply (@fold_rec_bis _ (fun s _ => P s) (fun _ _ _ => tt) tt m); eauto.
  Qed.

  (** [fold] can be used to reconstruct the same initial set. *)

  Lemma fold_identity : forall m : t elt, Equal (fold (@add _) m (empty _)) m.
  Proof.
  intros.
  apply fold_rec with (P:=fun m acc => Equal acc m); auto with map.
  intros m' Heq k'.
  rewrite empty_o.
  case_eq (find k' m'); auto; intros e'; rewrite <- find_mapsto_iff.
  intro; elim (Heq k' e'); auto.
  intros k e a m' m'' _ _ Hadd Heq k'.
  red in Heq. rewrite Hadd, 2 add_o, Heq; auto.
  Qed.

  Section Fold_More.

  (** ** Additional properties of fold *)

  (** When a function [f] is compatible and allows transpositions, we can
      compute [fold f] in any order. *)

  Variables (A:Type)(eqA:A->A->Prop)(st:Equivalence eqA)(f:key->elt->A->A).

  (** This is more convenient than a [compat_op eqke ...].
      In fact, every [compat_op], [compat_bool], etc, should
      become a [Proper] someday. *)
  Hypothesis Comp : Proper (E.eq==>eq==>eqA==>eqA) f.

  Lemma fold_init :
   forall m i i', eqA i i' -> eqA (fold f m i) (fold f m i').
  Proof.
  intros. apply fold_rel with (R:=eqA); auto.
  intros. apply Comp; auto.
  Qed.

  Lemma fold_Empty :
   forall m i, Empty m -> eqA (fold f m i) i.
  Proof.
  intros. apply fold_rec_nodep with (P:=fun a => eqA a i).
  reflexivity.
  intros. elim (H k e); auto.
  Qed.

  (** As noticed by P. Casteran, asking for the general [SetoidList.transpose]
      here is too restrictive. Think for instance of [f] being [M.add] :
      in general, [M.add k e (M.add k e' m)] is not equivalent to
      [M.add k e' (M.add k e m)]. Fortunately, we will never encounter this
      situation during a real [fold], since the keys received by this [fold]
      are unique. Hence we can ask the transposition property to hold only
      for non-equal keys.

      This idea could be push slightly further, by asking the transposition
      property to hold only for (non-equal) keys living in the map given to
      [fold]. Please contact us if you need such a version.

      FSets could also benefit from a restricted [transpose], but for this
      case the gain is unclear. *)

  Definition transpose_neqkey :=
    forall k k' e e' a, ~E.eq k k' ->
      eqA (f k e (f k' e' a)) (f k' e' (f k e a)).

  Hypothesis Tra : transpose_neqkey.

  Lemma fold_commutes : forall i m k e, ~In k m ->
   eqA (fold f m (f k e i)) (f k e (fold f m i)).
  Proof.
  intros i m k e Hnotin.
  apply fold_rel with (R:= fun a b => eqA a (f k e b)); auto.
  reflexivity.
  intros.
  transitivity (f k0 e0 (f k e b)).
  apply Comp; auto.
  apply Tra; auto.
  contradict Hnotin; rewrite <- Hnotin; exists e0; auto.
  Qed.

  Hint Resolve NoDupA_eqk_eqke NoDupA_rev elements_3w : map.

  Lemma fold_Equal : forall m1 m2 i, Equal m1 m2 ->
   eqA (fold f m1 i) (fold f m2 i).
  Proof.
  intros.
  rewrite 2 fold_spec_right.
  assert (NoDupA eqk (rev (elements m1))) by (auto with *).
  assert (NoDupA eqk (rev (elements m2))) by (auto with *).
  apply fold_right_equivlistA_restr with (R:=complement eqk)(eqA:=eqke);
   auto with *.
  intros (k1,e1) (k2,e2) (Hk,He) a1 a2 Ha; simpl in *; apply Comp; auto.
  unfold complement, eq_key, eq_key_elt; repeat red. intuition eauto.
  intros (k,e) (k',e'); unfold eq_key, uncurry; simpl; auto.
  rewrite <- NoDupA_altdef; auto.
  intros (k,e).
  rewrite 2 InA_rev, <- 2 elements_mapsto_iff, 2 find_mapsto_iff, H;
   auto with *.
  Qed.

  Lemma fold_Equal2 : forall m1 m2 i j, Equal m1 m2 -> eqA i j ->
    eqA (fold f m1 i) (fold f m2 j).
  Proof.
  intros.
  rewrite 2 fold_spec_right.
  assert (NoDupA eqk (rev (elements m1))) by (auto with * ).
  assert (NoDupA eqk (rev (elements m2))) by (auto with * ).
  apply fold_right_equivlistA_restr2 with (R:=complement eqk)(eqA:=eqke)
  ; auto with *.
  - intros (k1,e1) (k2,e2) (Hk,He) a1 a2 Ha; simpl in *; apply Comp; auto.
  - unfold complement, eq_key, eq_key_elt; repeat red. intuition eauto.
  - intros (k,e) (k',e') z z' h h'; unfold eq_key, uncurry;simpl; auto.
    rewrite h'.
    auto.
  - rewrite <- NoDupA_altdef; auto.
  - intros (k,e).
    rewrite 2 InA_rev, <- 2 elements_mapsto_iff, 2 find_mapsto_iff, H;
      auto with *.
  Qed.


  Lemma fold_Add : forall m1 m2 k e i, ~In k m1 -> Add k e m1 m2 ->
   eqA (fold f m2 i) (f k e (fold f m1 i)).
  Proof.
  intros.
  rewrite 2 fold_spec_right.
  set (f':=uncurry f).
  change (f k e (fold_right f' i (rev (elements m1))))
   with (f' (k,e) (fold_right f' i (rev (elements m1)))).
  assert (NoDupA eqk (rev (elements m1))) by (auto with *).
  assert (NoDupA eqk (rev (elements m2))) by (auto with *).
  apply fold_right_add_restr with
   (R:=complement eqk)(eqA:=eqke)(eqB:=eqA); auto with *.
  intros (k1,e1) (k2,e2) (Hk,He) a a' Ha; unfold f'; simpl in *. apply Comp; auto.
  unfold complement, eq_key_elt, eq_key; repeat red; intuition eauto.
  unfold f'; intros (k1,e1) (k2,e2); unfold eq_key, uncurry; simpl; auto.
  rewrite <- NoDupA_altdef; auto.
  rewrite InA_rev, <- elements_mapsto_iff by (auto with *). firstorder.
  intros (a,b).
  rewrite InA_cons, 2 InA_rev, <- 2 elements_mapsto_iff,
   2 find_mapsto_iff by (auto with *).
  unfold eq_key_elt; simpl.
  rewrite H0.
  rewrite add_o.
  destruct (eq_dec k a) as [EQ|NEQ]; split; auto.
  intros EQ'; inversion EQ'; auto.
  intuition; subst; auto.
  elim H. exists b; rewrite EQ; auto with map.
  intuition.
  elim NEQ; auto.
  Qed.

  Lemma fold_add : forall m k e i, ~In k m ->
   eqA (fold f (add k e m) i) (f k e (fold f m i)).
  Proof.
  intros. apply fold_Add; try red; auto.
  Qed.

  End Fold_More.

  (** * Cardinal *)

  Lemma cardinal_fold : forall m : t elt,
   cardinal m = fold (fun _ _ => S) m 0.
  Proof.
  intros; rewrite cardinal_1, fold_1.
  symmetry; apply fold_left_length; auto.
  Qed.

  Lemma cardinal_Empty : forall m : t elt,
   Empty m <-> cardinal m = 0.
  Proof.
  intros.
  rewrite cardinal_1, elements_Empty.
  destruct (elements m); intuition; discriminate.
  Qed.

  Lemma Equal_cardinal : forall m m' : t elt,
    Equal m m' -> cardinal m = cardinal m'.
  Proof.
  intros; do 2 rewrite cardinal_fold.
  apply fold_Equal with (eqA:=eq); compute; auto.
  Qed.

  Lemma cardinal_1 : forall m : t elt, Empty m -> cardinal m = 0.
  Proof.
  intros; rewrite <- cardinal_Empty; auto.
  Qed.

  Lemma cardinal_2 :
    forall m m' x e, ~ In x m -> Add x e m m' -> cardinal m' = S (cardinal m).
  Proof.
  intros; do 2 rewrite cardinal_fold.
  change S with ((fun _ _ => S) x e).
  apply fold_Add with (eqA:=eq); compute; auto.
  Qed.

  Lemma cardinal_inv_1 : forall m : t elt,
   cardinal m = 0 -> Empty m.
  Proof.
  intros; rewrite cardinal_Empty; auto.
  Qed.
  Hint Resolve cardinal_inv_1 : map.

  Lemma cardinal_inv_2 :
   forall m n, cardinal m = S n -> { p : key*elt | MapsTo (fst p) (snd p) m }.
  Proof.
  intros; rewrite M.cardinal_1 in *.
  generalize (elements_mapsto_iff m).
  destruct (elements m); try discriminate.
  exists p; auto.
  rewrite H0; destruct p; simpl; auto.
  constructor; red; auto.
  Qed.

  Lemma cardinal_inv_2b :
   forall m, cardinal m <> 0 -> { p : key*elt | MapsTo (fst p) (snd p) m }.
  Proof.
  intros.
  generalize (@cardinal_inv_2 m); destruct cardinal.
  elim H;auto.
  eauto.
  Qed.

  (** * Additional notions over maps *)

  Definition Disjoint (m m' : t elt) :=
   forall k, ~(In k m /\ In k m').

  Definition Partition (m m1 m2 : t elt) :=
    Disjoint m1 m2 /\
    (forall k e, MapsTo k e m <-> MapsTo k e m1 \/ MapsTo k e m2).

  (** * Emulation of some functions lacking in the interface *)

  Definition filter (f : key -> elt -> bool)(m : t elt) :=
   fold (fun k e m => if f k e then add k e m else m) m (empty _).

  Definition for_all (f : key -> elt -> bool)(m : t elt) :=
   fold (fun k e b => if f k e then b else false) m true.

  Definition exists_ (f : key -> elt -> bool)(m : t elt) :=
   fold (fun k e b => if f k e then true else b) m false.

  Definition partition (f : key -> elt -> bool)(m : t elt) :=
   (filter f m, filter (fun k e => negb (f k e)) m).

  (** [update] adds to [m1] all the bindings of [m2]. It can be seen as
     an [union] operator which gives priority to its 2nd argument
     in case of binding conflit. *)

  Definition update (m1 m2 : t elt) := fold (@add _) m2 m1.

  (** [restrict] keeps from [m1] only the bindings whose key is in [m2].
      It can be seen as an [inter] operator, with priority to its 1st argument
      in case of binding conflit. *)

  Definition restrict (m1 m2 : t elt) := filter (fun k _ => mem k m2) m1.

  (** [diff] erases from [m1] all bindings whose key is in [m2]. *)

  Definition diff (m1 m2 : t elt) := filter (fun k _ => negb (mem k m2)) m1.

  Section Specs.
  Variable f : key -> elt -> bool.
  Hypothesis Hf : Proper (E.eq==>eq==>eq) f.

  Lemma filter_iff : forall m k e,
   MapsTo k e (filter f m) <-> MapsTo k e m /\ f k e = true.
  Proof.
  unfold filter.
  set (f':=fun k e m => if f k e then add k e m else m).
  intro m. pattern m, (fold f' m (empty _)). apply fold_rec.

  intros m' Hm' k e. rewrite empty_mapsto_iff. intuition.
  elim (Hm' k e); auto.

  intros k e acc m1 m2 Hke Hn Hadd IH k' e'.
  change (Equal m2 (add k e m1)) in Hadd; rewrite Hadd.
  unfold f'; simpl.
  case_eq (f k e); intros Hfke; simpl;
   rewrite !add_mapsto_iff, IH; clear IH; intuition.
  rewrite <- Hfke; apply Hf; auto.
  destruct (eq_dec k k') as [Hk|Hk]; [left|right]; auto.
  elim Hn; exists e'; rewrite Hk; auto.
  assert (f k e = f k' e') by (apply Hf; auto). congruence.
  Qed.

  Lemma for_all_iff : forall m,
   for_all f m = true <-> (forall k e, MapsTo k e m -> f k e = true).
  Proof.
  unfold for_all.
  set (f':=fun k e b => if f k e then b else false).
  intro m. pattern m, (fold f' m true). apply fold_rec.

  intros m' Hm'. split; auto. intros _ k e Hke. elim (Hm' k e); auto.

  intros k e b m1 m2 _ Hn Hadd IH. clear m.
  change (Equal m2 (add k e m1)) in Hadd.
  unfold f'; simpl. case_eq (f k e); intros Hfke.
  (* f k e = true *)
  rewrite IH. clear IH. split; intros Hmapsto k' e' Hke'.
  rewrite Hadd, add_mapsto_iff in Hke'.
  destruct Hke' as [(?,?)|(?,?)]; auto.
  rewrite <- Hfke; apply Hf; auto.
  apply Hmapsto. rewrite Hadd, add_mapsto_iff; right; split; auto.
  contradict Hn; exists e'; rewrite Hn; auto.
  (* f k e = false *)
  split; try discriminate.
  intros Hmapsto. rewrite <- Hfke. apply Hmapsto.
  rewrite Hadd, add_mapsto_iff; auto.
  Qed.

  Lemma exists_iff : forall m,
   exists_ f m = true <->
   (exists p, MapsTo (fst p) (snd p) m /\ f (fst p) (snd p) = true).
  Proof.
  unfold exists_.
  set (f':=fun k e b => if f k e then true else b).
  intro m. pattern m, (fold f' m false). apply fold_rec.

  intros m' Hm'. split; try discriminate.
  intros ((k,e),(Hke,_)); simpl in *. elim (Hm' k e); auto.

  intros k e b m1 m2 _ Hn Hadd IH. clear m.
  change (Equal m2 (add k e m1)) in Hadd.
  unfold f'; simpl. case_eq (f k e); intros Hfke.
  (* f k e = true *)
  split; [intros _|auto].
  exists (k,e); simpl; split; auto.
  rewrite Hadd, add_mapsto_iff; auto.
  (* f k e = false *)
  rewrite IH. clear IH. split; intros ((k',e'),(Hke1,Hke2)); simpl in *.
  exists (k',e'); simpl; split; auto.
  rewrite Hadd, add_mapsto_iff; right; split; auto.
  contradict Hn. exists e'; rewrite Hn; auto.
  rewrite Hadd, add_mapsto_iff in Hke1. destruct Hke1 as [(?,?)|(?,?)].
  assert (f k' e' = f k e) by (apply Hf; auto). congruence.
  exists (k',e'); auto.
  Qed.

  End Specs.

  Lemma Disjoint_alt : forall m m',
   Disjoint m m' <->
   (forall k e e', MapsTo k e m -> MapsTo k e' m' -> False).
  Proof.
  unfold Disjoint; split.
  intros H k v v' H1 H2.
  apply H with k; split.
  exists v; trivial.
  exists v'; trivial.
  intros H k ((v,Hv),(v',Hv')).
  eapply H; eauto.
  Qed.

  Section Partition.
  Variable f : key -> elt -> bool.
  Hypothesis Hf : Proper (E.eq==>eq==>eq) f.

  Lemma partition_iff_1 : forall m m1 k e,
   m1 = fst (partition f m) ->
   (MapsTo k e m1 <-> MapsTo k e m /\ f k e = true).
  Proof.
  unfold partition; simpl; intros. subst m1.
  apply filter_iff; auto.
  Qed.

  Lemma partition_iff_2 : forall m m2 k e,
   m2 = snd (partition f m) ->
   (MapsTo k e m2 <-> MapsTo k e m /\ f k e = false).
  Proof.
  unfold partition; simpl; intros. subst m2.
  rewrite filter_iff.
  split; intros (H,H'); split; auto.
  destruct (f k e); simpl in *; auto.
  rewrite H'; auto.
  repeat red; intros. f_equal. apply Hf; auto.
  Qed.

  Lemma partition_Partition : forall m m1 m2,
   partition f m = (m1,m2) -> Partition m m1 m2.
  Proof.
  intros. split.
  rewrite Disjoint_alt. intros k e e'.
  rewrite (@partition_iff_1 m m1), (@partition_iff_2 m m2)
   by (rewrite H; auto).
  intros (U,V) (W,Z). rewrite <- (MapsTo_fun U W) in Z; congruence.
  intros k e.
  rewrite (@partition_iff_1 m m1), (@partition_iff_2 m m2)
   by (rewrite H; auto).
  destruct (f k e); intuition.
  Qed.

  End Partition.

  Lemma Partition_In : forall m m1 m2 k,
   Partition m m1 m2 -> In k m -> {In k m1}+{In k m2}.
  Proof.
  intros m m1 m2 k Hm Hk.
  destruct (In_dec m1 k) as [H|H]; [left|right]; auto.
  destruct Hm as (Hm,Hm').
  destruct Hk as (e,He); rewrite Hm' in He; destruct He.
  elim H; exists e; auto.
  exists e; auto.
  Defined.

  Lemma Disjoint_sym : forall m1 m2, Disjoint m1 m2 -> Disjoint m2 m1.
  Proof.
  intros m1 m2 H k (H1,H2). elim (H k); auto.
  Qed.

  Lemma Partition_sym : forall m m1 m2,
   Partition m m1 m2 -> Partition m m2 m1.
  Proof.
  intros m m1 m2 (H,H'); split.
  apply Disjoint_sym; auto.
  intros; rewrite H'; intuition.
  Qed.

  Lemma Partition_Empty : forall m m1 m2, Partition m m1 m2 ->
   (Empty m <-> (Empty m1 /\ Empty m2)).
  Proof.
  intros m m1 m2 (Hdisj,Heq). split.
  intro He.
  split; intros k e Hke; elim (He k e); rewrite Heq; auto.
  intros (He1,He2) k e Hke. rewrite Heq in Hke. destruct Hke.
  elim (He1 k e); auto.
  elim (He2 k e); auto.
  Qed.

  Lemma Partition_Add :
    forall m m' x e , ~In x m -> Add x e m m' ->
    forall m1 m2, Partition m' m1 m2 ->
     exists m3, (Add x e m3 m1 /\ Partition m m3 m2 \/
                 Add x e m3 m2 /\ Partition m m1 m3).
  Proof.
  unfold Partition. intros m m' x e Hn Hadd m1 m2 (Hdisj,Hor).
  assert (Heq : Equal m (remove x m')).
   change (Equal m' (add x e m)) in Hadd. rewrite Hadd.
   intro k. rewrite remove_o, add_o.
   destruct eq_dec as [He|Hne]; auto.
   rewrite <- He, <- not_find_in_iff; auto.
  assert (H : MapsTo x e m').
   change (Equal m' (add x e m)) in Hadd; rewrite Hadd.
   apply add_1; auto.
  rewrite Hor in H; destruct H.

  (* first case : x in m1 *)
  exists (remove x m1); left. split; [|split].
  (* add *)
  change (Equal m1 (add x e (remove x m1))).
  intro k.
  rewrite add_o, remove_o.
  destruct eq_dec as [He|Hne]; auto.
  rewrite <- He; apply find_1; auto.
  (* disjoint *)
  intros k (H1,H2). elim (Hdisj k). split; auto.
  rewrite remove_in_iff in H1; destruct H1; auto.
  (* mapsto *)
  intros k' e'.
  rewrite Heq, 2 remove_mapsto_iff, Hor.
  intuition.
  elim (Hdisj x); split; [exists e|exists e']; auto.
  apply MapsTo_1 with k'; auto.

  (* second case : x in m2 *)
  exists (remove x m2); right. split; [|split].
  (* add *)
  change (Equal m2 (add x e (remove x m2))).
  intro k.
  rewrite add_o, remove_o.
  destruct eq_dec as [He|Hne]; auto.
  rewrite <- He; apply find_1; auto.
  (* disjoint *)
  intros k (H1,H2). elim (Hdisj k). split; auto.
  rewrite remove_in_iff in H2; destruct H2; auto.
  (* mapsto *)
  intros k' e'.
  rewrite Heq, 2 remove_mapsto_iff, Hor.
  intuition.
  elim (Hdisj x); split; [exists e'|exists e]; auto.
  apply MapsTo_1 with k'; auto.
  Qed.

  Lemma Partition_fold :
   forall (A:Type)(eqA:A->A->Prop)(st:Equivalence eqA)(f:key->elt->A->A),
   Proper (E.eq==>eq==>eqA==>eqA) f ->
   transpose_neqkey eqA f ->
   forall m m1 m2 i,
   Partition m m1 m2 ->
   eqA (fold f m i) (fold f m1 (fold f m2 i)).
  Proof.
  intros A eqA st f Comp Tra.
  induction m as [m Hm|m m' IH k e Hn Hadd] using map_induction.

  intros m1 m2 i Hp. rewrite (fold_Empty (eqA:=eqA)); auto.
  rewrite (Partition_Empty Hp) in Hm. destruct Hm.
  rewrite 2 (fold_Empty (eqA:=eqA)); auto. reflexivity.

  intros m1 m2 i Hp.
  destruct (Partition_Add Hn Hadd Hp) as (m3,[(Hadd',Hp')|(Hadd',Hp')]).
  (* fst case: m3 is (k,e)::m1 *)
  assert (~In k m3).
   contradict Hn. destruct Hn as (e',He').
   destruct Hp' as (Hp1,Hp2). exists e'. rewrite Hp2; auto.
  transitivity (f k e (fold f m i)).
  apply fold_Add with (eqA:=eqA); auto.
  symmetry.
  transitivity (f k e (fold f m3 (fold f m2 i))).
  apply fold_Add with (eqA:=eqA); auto.
  apply Comp; auto.
  symmetry; apply IH; auto.
  (* snd case: m3 is (k,e)::m2 *)
  assert (~In k m3).
   contradict Hn. destruct Hn as (e',He').
   destruct Hp' as (Hp1,Hp2). exists e'. rewrite Hp2; auto.
  assert (~In k m1).
   contradict Hn. destruct Hn as (e',He').
   destruct Hp' as (Hp1,Hp2). exists e'. rewrite Hp2; auto.
  transitivity (f k e (fold f m i)).
  apply fold_Add with (eqA:=eqA); auto.
  transitivity (f k e (fold f m1 (fold f m3 i))).
  apply Comp; auto using IH.
  transitivity (fold f m1 (f k e (fold f m3 i))).
  symmetry.
  apply fold_commutes with (eqA:=eqA); auto.
  apply fold_init with (eqA:=eqA); auto.
  symmetry.
  apply fold_Add with (eqA:=eqA); auto.
  Qed.

  Lemma Partition_cardinal : forall m m1 m2, Partition m m1 m2 ->
   cardinal m = cardinal m1 + cardinal m2.
  Proof.
  intros.
  rewrite (cardinal_fold m), (cardinal_fold m1).
  set (f:=fun (_:key)(_:elt)=>S).
  setoid_replace (fold f m 0) with (fold f m1 (fold f m2 0)).
  rewrite <- cardinal_fold.
  apply fold_rel with (R:=fun u v => u = v + cardinal m2); simpl; auto.
  apply Partition_fold with (eqA:=eq); repeat red; auto.
  Qed.

  Lemma Partition_partition : forall m m1 m2, Partition m m1 m2 ->
    let f := fun k (_:elt) => mem k m1 in
   Equal m1 (fst (partition f m)) /\ Equal m2 (snd (partition f m)).
  Proof.
  intros m m1 m2 Hm f.
  assert (Hf : Proper (E.eq==>eq==>eq) f).
   intros k k' Hk e e' _; unfold f; rewrite Hk; auto.
  set (m1':= fst (partition f m)).
  set (m2':= snd (partition f m)).
  split; rewrite Equal_mapsto_iff; intros k e.
  rewrite (@partition_iff_1 f Hf m m1') by auto.
  unfold f.
  rewrite <- mem_in_iff.
  destruct Hm as (Hm,Hm').
  rewrite Hm'.
  intuition.
  exists e; auto.
  elim (Hm k); split; auto; exists e; auto.
  rewrite (@partition_iff_2 f Hf m m2') by auto.
  unfold f.
  rewrite <- not_mem_in_iff.
  destruct Hm as (Hm,Hm').
  rewrite Hm'.
  intuition.
  elim (Hm k); split; auto; exists e; auto.
  elim H1; exists e; auto.
  Qed.

  Lemma update_mapsto_iff : forall m m' k e,
   MapsTo k e (update m m') <->
    (MapsTo k e m' \/ (MapsTo k e m /\ ~In k m')).
  Proof.
  unfold update.
  intros m m'.
  pattern m', (fold (@add _) m' m). apply fold_rec.

  intros m0 Hm0 k e.
  assert (~In k m0) by (intros (e0,He0); apply (Hm0 k e0); auto).
  intuition.
  elim (Hm0 k e); auto.

  intros k e m0 m1 m2 _ Hn Hadd IH k' e'.
  change (Equal m2 (add k e m1)) in Hadd.
  rewrite Hadd, 2 add_mapsto_iff, IH, add_in_iff. clear IH. intuition.
  Qed.

  Lemma update_dec : forall m m' k e, MapsTo k e (update m m') ->
   { MapsTo k e m' } + { MapsTo k e m /\ ~In k m'}.
  Proof.
  intros m m' k e H. rewrite update_mapsto_iff in H.
  destruct (In_dec m' k) as [H'|H']; [left|right]; intuition.
  elim H'; exists e; auto.
  Defined.

  Lemma update_in_iff : forall m m' k,
   In k (update m m') <-> In k m \/ In k m'.
  Proof.
  intros m m' k. split.
  intros (e,H); rewrite update_mapsto_iff in H.
  destruct H; [right|left]; exists e; intuition.
  destruct (In_dec m' k) as [H|H].
  destruct H as (e,H). intros _; exists e.
  rewrite update_mapsto_iff; left; auto.
  destruct 1 as [H'|H']; [|elim H; auto].
  destruct H' as (e,H'). exists e.
  rewrite update_mapsto_iff; right; auto.
  Qed.

  Lemma diff_mapsto_iff : forall m m' k e,
   MapsTo k e (diff m m') <-> MapsTo k e m /\ ~In k m'.
  Proof.
  intros m m' k e.
  unfold diff.
  rewrite filter_iff.
  intuition.
  rewrite mem_1 in *; auto; discriminate.
  intros ? ? Hk _ _ _; rewrite Hk; auto.
  Qed.

  Lemma diff_in_iff : forall m m' k,
   In k (diff m m') <-> In k m /\ ~In k m'.
  Proof.
  intros m m' k. split.
  intros (e,H); rewrite diff_mapsto_iff in H.
  destruct H; split; auto. exists e; auto.
  intros ((e,H),H'); exists e; rewrite diff_mapsto_iff; auto.
  Qed.

  Lemma restrict_mapsto_iff : forall m m' k e,
   MapsTo k e (restrict m m') <-> MapsTo k e m /\ In k m'.
  Proof.
  intros m m' k e.
  unfold restrict.
  rewrite filter_iff.
  intuition.
  intros ? ? Hk _ _ _; rewrite Hk; auto.
  Qed.

  Lemma restrict_in_iff : forall m m' k,
   In k (restrict m m') <-> In k m /\ In k m'.
  Proof.
  intros m m' k. split.
  intros (e,H); rewrite restrict_mapsto_iff in H.
  destruct H; split; auto. exists e; auto.
  intros ((e,H),H'); exists e; rewrite restrict_mapsto_iff; auto.
  Qed.

  (** specialized versions analyzing only keys (resp. elements) *)

  Definition filter_dom (f : key -> bool) := filter (fun k _ => f k).
  Definition filter_range (f : elt -> bool) := filter (fun _ => f).
  Definition for_all_dom (f : key -> bool) := for_all (fun k _ => f k).
  Definition for_all_range (f : elt -> bool) := for_all (fun _ => f).
  Definition exists_dom (f : key -> bool) := exists_ (fun k _ => f k).
  Definition exists_range (f : elt -> bool) := exists_ (fun _ => f).
  Definition partition_dom (f : key -> bool) := partition (fun k _ => f k).
  Definition partition_range (f : elt -> bool) := partition (fun _ => f).

 End Elt.

 Add Parametric Morphism elt : (@cardinal elt)
   with signature Equal ==> eq as cardinal_m.
 Proof. intros; apply Equal_cardinal; auto. Qed.

 Add Parametric Morphism elt : (@Disjoint elt)
   with signature Equal ==> Equal ==> iff as Disjoint_m.
 Proof.
  intros m1 m1' Hm1 m2 m2' Hm2. unfold Disjoint. split; intros.
  rewrite <- Hm1, <- Hm2; auto.
  rewrite Hm1, Hm2; auto.
 Qed.

 Add Parametric Morphism elt : (@Partition elt)
   with signature Equal ==> Equal ==> Equal ==> iff as Partition_m.
 Proof.
  intros m1 m1' Hm1 m2 m2' Hm2 m3 m3' Hm3. unfold Partition.
  rewrite <- Hm2, <- Hm3.
  split; intros (H,H'); split; auto; intros.
  rewrite <- Hm1, <- Hm2, <- Hm3; auto.
  rewrite Hm1, Hm2, Hm3; auto.
 Qed.

 Add Parametric Morphism elt : (@update elt)
   with signature Equal ==> Equal ==> Equal as update_m.
 Proof.
  intros m1 m1' Hm1 m2 m2' Hm2.
  setoid_replace (update m1 m2) with (update m1' m2); unfold update.
  apply fold_Equal with (eqA:=Equal); auto.
  intros k k' Hk e e' He m m' Hm; rewrite Hk,He,Hm; red; auto.
  intros k k' e e' i Hneq x.
  rewrite !add_o; do 2 destruct eq_dec; auto. elim Hneq; eauto.
  apply fold_init with (eqA:=Equal); auto.
  intros k k' Hk e e' He m m' Hm; rewrite Hk,He,Hm; red; auto.
 Qed.

 Add Parametric Morphism elt : (@restrict elt)
   with signature Equal ==> Equal ==> Equal as restrict_m.
 Proof.
  intros m1 m1' Hm1 m2 m2' Hm2.
  setoid_replace (restrict m1 m2) with (restrict m1' m2);
   unfold restrict, filter.
  apply fold_rel with (R:=Equal); try red; auto.
   intros k e i i' H Hii' x.
   pattern (mem k m2); rewrite Hm2. (* UGLY, see with Matthieu *)
   destruct mem; rewrite Hii'; auto.
  apply fold_Equal with (eqA:=Equal); auto.
   intros k k' Hk e e' He m m' Hm; simpl in *.
   pattern (mem k m2); rewrite Hk. (* idem *)
   destruct mem; rewrite ?Hk,?He,Hm; red; auto.
   intros k k' e e' i Hneq x.
   case_eq (mem k m2); case_eq (mem k' m2); intros; auto.
   rewrite !add_o; do 2 destruct eq_dec; auto. elim Hneq; eauto.
 Qed.

 Add Parametric Morphism elt : (@diff elt)
   with signature Equal ==> Equal ==> Equal as diff_m.
 Proof.
  intros m1 m1' Hm1 m2 m2' Hm2.
  setoid_replace (diff m1 m2) with (diff m1' m2);
   unfold diff, filter.
  apply fold_rel with (R:=Equal); try red; auto.
   intros k e i i' H Hii' x.
   pattern (mem k m2); rewrite Hm2. (* idem *)
   destruct mem; simpl; rewrite Hii'; auto.
  apply fold_Equal with (eqA:=Equal); auto.
   intros k k' Hk e e' He m m' Hm; simpl in *.
   pattern (mem k m2); rewrite Hk. (* idem *)
   destruct mem; simpl; rewrite ?Hk,?He,Hm; red; auto.
   intros k k' e e' i Hneq x.
   case_eq (mem k m2); case_eq (mem k' m2); intros; simpl; auto.
   rewrite !add_o; do 2 destruct eq_dec; auto. elim Hneq; eauto.
 Qed.

End WProperties_fun.

(** * Same Properties for self-contained weak maps and for full maps *)

Module WProperties (M:WS) := WProperties_fun M.E M.
Module Properties := WProperties.

(** * Properties specific to maps with ordered keys *)

Module OrdProperties (M:S).
 Module Import ME := OrderedTypeFacts M.E.
 Module Import O:=KeyOrderedType M.E.
 Module Import P:=Properties M.
 Import F.
 Import M.

 Section Elt.
  Variable elt:Type.

  Notation eqke := (@eqke elt).
  Notation eqk := (@eqk elt).
  Notation ltk := (@ltk elt).
  Notation cardinal := (@cardinal elt).
  Notation Equal := (@Equal elt).
  Notation Add := (@Add elt).

  Definition Above x (m:t elt) := forall y, In y m -> E.lt y x.
  Definition Below x (m:t elt) := forall y, In y m -> E.lt x y.

  Section Elements.

  Lemma sort_equivlistA_eqlistA : forall l l' : list (key*elt),
   sort ltk l -> sort ltk l' -> equivlistA eqke l l' -> eqlistA eqke l l'.
  Proof.
  apply SortA_equivlistA_eqlistA; eauto with *.
  Qed.

  Ltac clean_eauto := unfold O.eqke, O.ltk; simpl; intuition; eauto.

  Definition gtb (p p':key*elt) :=
    match E.compare (fst p) (fst p') with GT _ => true | _ => false end.
  Definition leb p := fun p' => negb (gtb p p').

  Definition elements_lt p m := List.filter (gtb p) (elements m).
  Definition elements_ge p m := List.filter (leb p) (elements m).

  Lemma gtb_1 : forall p p', gtb p p' = true <-> ltk p' p.
  Proof.
   intros (x,e) (y,e'); unfold gtb, O.ltk; simpl.
   destruct (E.compare x y); intuition; try discriminate; ME.order.
  Qed.

  Lemma leb_1 : forall p p', leb p p' = true <-> ~ltk p' p.
  Proof.
   intros (x,e) (y,e'); unfold leb, gtb, O.ltk; simpl.
   destruct (E.compare x y); intuition; try discriminate; ME.order.
  Qed.

  Lemma gtb_compat : forall p, Proper (eqke==>eq) (gtb p).
  Proof.
   red; intros (x,e) (a,e') (b,e'') H; red in H; simpl in *; destruct H.
   generalize (gtb_1 (x,e) (a,e'))(gtb_1 (x,e) (b,e''));
    destruct (gtb (x,e) (a,e')); destruct (gtb (x,e) (b,e'')); auto.
   unfold O.ltk in *; simpl in *; intros.
   symmetry; rewrite H2.
   apply ME.eq_lt with a; auto.
   rewrite <- H1; auto.
   unfold O.ltk in *; simpl in *; intros.
   rewrite H1.
   apply ME.eq_lt with b; auto.
   rewrite <- H2; auto.
  Qed.

  Lemma leb_compat : forall p, Proper (eqke==>eq) (leb p).
  Proof.
   red; intros x a b H.
   unfold leb; f_equal; apply gtb_compat; auto.
  Qed.

  Hint Resolve gtb_compat leb_compat elements_3 : map.

  Lemma elements_split : forall p m,
    elements m = elements_lt p m ++ elements_ge p m.
  Proof.
  unfold elements_lt, elements_ge, leb; intros.
  apply filter_split with (eqA:=eqk) (ltA:=ltk); eauto with *.
  intros; destruct x; destruct y; destruct p.
  rewrite gtb_1 in H; unfold O.ltk in H; simpl in *.
  assert (~ltk (t1,e0) (k,e1)).
   unfold gtb, O.ltk in *; simpl in *.
   destruct (E.compare k t1); intuition; try discriminate; ME.order.
  unfold O.ltk in *; simpl in *; ME.order.
  Qed.

  Lemma elements_Add : forall m m' x e, ~In x m -> Add x e m m' ->
    eqlistA eqke (elements m')
                 (elements_lt (x,e) m ++ (x,e):: elements_ge (x,e) m).
  Proof.
  intros; unfold elements_lt, elements_ge.
  apply sort_equivlistA_eqlistA; auto with *.
  apply (@SortA_app _ eqke); auto with *.
  apply (@filter_sort _ eqke); auto with *; clean_eauto.
  constructor; auto with map.
  apply (@filter_sort _ eqke); auto with *; clean_eauto.
  rewrite (@InfA_alt _ eqke); auto with *; try (clean_eauto; fail).
  intros.
  rewrite filter_InA in H1; auto with *; destruct H1.
  rewrite leb_1 in H2.
  destruct y; unfold O.ltk in *; simpl in *.
  rewrite <- elements_mapsto_iff in H1.
  assert (~E.eq x t0).
   contradict H.
   exists e0; apply MapsTo_1 with t0; auto.
  ME.order.
  apply (@filter_sort _ eqke); auto with *; clean_eauto.
  intros.
  rewrite filter_InA in H1; auto with *; destruct H1.
  rewrite gtb_1 in H3.
  destruct y; destruct x0; unfold O.ltk in *; simpl in *.
  inversion_clear H2.
  red in H4; simpl in *; destruct H4.
  ME.order.
  rewrite filter_InA in H4; auto with *; destruct H4.
  rewrite leb_1 in H4.
  unfold O.ltk in *; simpl in *; ME.order.
  red; intros a; destruct a.
  rewrite InA_app_iff, InA_cons, 2 filter_InA,
    <-2 elements_mapsto_iff, leb_1, gtb_1,
    find_mapsto_iff, (H0 t0), <- find_mapsto_iff,
    add_mapsto_iff by (auto with *).
  unfold O.eqke, O.ltk; simpl.
  destruct (E.compare t0 x); intuition; try fold (~E.eq x t0); auto.
  - elim H; exists e0; apply MapsTo_1 with t0; auto.
  - fold (~E.lt t0 x); auto.
  Qed.

  Lemma elements_Add_Above : forall m m' x e,
   Above x m -> Add x e m m' ->
     eqlistA eqke (elements m') (elements m ++ (x,e)::nil).
  Proof.
  intros.
  apply sort_equivlistA_eqlistA; auto with *.
  apply (@SortA_app _ eqke); auto with *.
  intros.
  inversion_clear H2.
  destruct x0; destruct y.
  rewrite <- elements_mapsto_iff in H1.
  unfold O.eqke, O.ltk in *; simpl in *; destruct H3.
  apply ME.lt_eq with x; auto.
  apply H; firstorder.
  inversion H3.
  red; intros a; destruct a.
  rewrite InA_app_iff, InA_cons, InA_nil, <- 2 elements_mapsto_iff,
   find_mapsto_iff, (H0 t0), <- find_mapsto_iff,
   add_mapsto_iff by (auto with *).
  unfold O.eqke; simpl. intuition.
  destruct (E.eq_dec x t0) as [Heq|Hneq]; auto.
  exfalso.
  assert (In t0 m).
   exists e0; auto.
  generalize (H t0 H1).
  ME.order.
  Qed.

  Lemma elements_Add_Below : forall m m' x e,
   Below x m -> Add x e m m' ->
     eqlistA eqke (elements m') ((x,e)::elements m).
  Proof.
  intros.
  apply sort_equivlistA_eqlistA; auto with *.
  change (sort ltk (((x,e)::nil) ++ elements m)).
  apply (@SortA_app _ eqke); auto with *.
  intros.
  inversion_clear H1.
  destruct y; destruct x0.
  rewrite <- elements_mapsto_iff in H2.
  unfold O.eqke, O.ltk in *; simpl in *; destruct H3.
  apply ME.eq_lt with x; auto.
  apply H; firstorder.
  inversion H3.
  red; intros a; destruct a.
  rewrite InA_cons, <- 2 elements_mapsto_iff,
    find_mapsto_iff, (H0 t0), <- find_mapsto_iff,
    add_mapsto_iff by (auto with *).
  unfold O.eqke; simpl. intuition.
  destruct (E.eq_dec x t0) as [Heq|Hneq]; auto.
  exfalso.
  assert (In t0 m).
   exists e0; auto.
  generalize (H t0 H1).
  ME.order.
  Qed.

  Lemma elements_Equal_eqlistA : forall (m m': t elt),
   Equal m m' -> eqlistA eqke (elements m) (elements m').
  Proof.
  intros.
  apply sort_equivlistA_eqlistA; auto with *.
  red; intros.
  destruct x; do 2 rewrite <- elements_mapsto_iff.
  do 2 rewrite find_mapsto_iff; rewrite H; split; auto.
  Qed.

  End Elements.

  Section Min_Max_Elt.

  (** We emulate two [max_elt] and [min_elt] functions. *)

  Fixpoint max_elt_aux (l:list (key*elt)) := match l with
    | nil => None
    | (x,e)::nil => Some (x,e)
    | (x,e)::l => max_elt_aux l
    end.
  Definition max_elt m := max_elt_aux (elements m).

  Lemma max_elt_Above :
   forall m x e, max_elt m = Some (x,e) -> Above x (remove x m).
  Proof.
  red; intros.
  rewrite remove_in_iff in H0.
  destruct H0.
  rewrite elements_in_iff in H1.
  destruct H1.
  unfold max_elt in *.
  generalize (elements_3 m).
  revert x e H y x0 H0 H1.
  induction (elements m).
  simpl; intros; try discriminate.
  intros.
  destruct a; destruct l; simpl in *.
  injection H as -> ->.
  inversion_clear H1.
  red in H; simpl in *; intuition.
  elim H0; eauto.
  inversion H.
  change (max_elt_aux (p::l) = Some (x,e)) in H.
  generalize (IHl x e H); clear IHl; intros IHl.
  inversion_clear H1; [ | inversion_clear H2; eauto ].
  red in H3; simpl in H3; destruct H3.
  destruct p as (p1,p2).
  destruct (E.eq_dec p1 x) as [Heq|Hneq].
  apply ME.lt_eq with p1; auto.
   inversion_clear H2.
   inversion_clear H5.
   red in H2; simpl in H2; ME.order.
  apply E.lt_trans with p1; auto.
   inversion_clear H2.
   inversion_clear H5.
   red in H2; simpl in H2; ME.order.
  eapply IHl; eauto.
  econstructor; eauto.
  red; eauto.
  inversion H2; auto.
  Qed.

  Lemma max_elt_MapsTo :
   forall m x e, max_elt m = Some (x,e) -> MapsTo x e m.
  Proof.
  intros.
  unfold max_elt in *.
  rewrite elements_mapsto_iff.
  induction (elements m).
  simpl; try discriminate.
  destruct a; destruct l; simpl in *.
  injection H; intros; subst; constructor; red; auto.
  constructor 2; auto.
  Qed.

  Lemma max_elt_Empty :
   forall m, max_elt m = None -> Empty m.
  Proof.
  intros.
  unfold max_elt in *.
  rewrite elements_Empty.
  induction (elements m); auto.
  destruct a; destruct l; simpl in *; try discriminate.
  assert (H':=IHl H); discriminate.
  Qed.

  Definition min_elt m : option (key*elt) := match elements m with
   | nil => None
   | (x,e)::_ => Some (x,e)
  end.

  Lemma min_elt_Below :
   forall m x e, min_elt m = Some (x,e) -> Below x (remove x m).
  Proof.
  unfold min_elt, Below; intros.
  rewrite remove_in_iff in H0; destruct H0.
  rewrite elements_in_iff in H1.
  destruct H1.
  generalize (elements_3 m).
  destruct (elements m).
  try discriminate.
  destruct p; injection H as -> ->; intros H4.
  inversion_clear H1 as [? ? H2|? ? H2].
  red in H2; destruct H2; simpl in *; ME.order.
  inversion_clear H4. rename H1 into H3.
  rewrite (@InfA_alt _ eqke) in H3; eauto with *.
  apply (H3 (y,x0)); auto.
  Qed.

  Lemma min_elt_MapsTo :
   forall m x e, min_elt m = Some (x,e) -> MapsTo x e m.
  Proof.
  intros.
  unfold min_elt in *.
  rewrite elements_mapsto_iff.
  destruct (elements m).
  simpl; try discriminate.
  destruct p; simpl in *.
  injection H; intros; subst; constructor; red; auto.
  Qed.

  Lemma min_elt_Empty :
   forall m, min_elt m = None -> Empty m.
  Proof.
  intros.
  unfold min_elt in *.
  rewrite elements_Empty.
  destruct (elements m); auto.
  destruct p; simpl in *; discriminate.
  Qed.

  End Min_Max_Elt.

  Section Induction_Principles.

  Lemma map_induction_max :
   forall P : t elt -> Type,
   (forall m, Empty m -> P m) ->
   (forall m m', P m -> forall x e, Above x m -> Add x e m m' -> P m') ->
   forall m, P m.
  Proof.
  intros; remember (cardinal m) as n; revert m Heqn; induction n; intros.
  apply X; apply cardinal_inv_1; auto.

  case_eq (max_elt m); intros.
  destruct p.
  assert (Add k e (remove k m) m).
   red; intros.
   rewrite add_o; rewrite remove_o; destruct (eq_dec k y); eauto.
   apply find_1; apply MapsTo_1 with k; auto.
   apply max_elt_MapsTo; auto.
  apply X0 with (remove k m) k e; auto with map.
  apply IHn.
  assert (S n = S (cardinal (remove k m))).
   rewrite Heqn.
   eapply cardinal_2; eauto with map.
  inversion H1; auto.
  eapply max_elt_Above; eauto.

  apply X; apply max_elt_Empty; auto.
  Qed.

  Lemma map_induction_min :
   forall P : t elt -> Type,
   (forall m, Empty m -> P m) ->
   (forall m m', P m -> forall x e, Below x m -> Add x e m m' -> P m') ->
   forall m, P m.
  Proof.
  intros; remember (cardinal m) as n; revert m Heqn; induction n; intros.
  apply X; apply cardinal_inv_1; auto.

  case_eq (min_elt m); intros.
  destruct p.
  assert (Add k e (remove k m) m).
   red; intros.
   rewrite add_o; rewrite remove_o; destruct (eq_dec k y); eauto.
   apply find_1; apply MapsTo_1 with k; auto.
   apply min_elt_MapsTo; auto.
  apply X0 with (remove k m) k e; auto.
  apply IHn.
  assert (S n = S (cardinal (remove k m))).
   rewrite Heqn.
   eapply cardinal_2; eauto with map.
  inversion H1; auto.
  eapply min_elt_Below; eauto.

  apply X; apply min_elt_Empty; auto.
  Qed.

  End Induction_Principles.

  Section Fold_properties.

  (** The following lemma has already been proved on Weak Maps,
      but with one additional hypothesis (some [transpose] fact). *)

  Lemma fold_Equal : forall m1 m2 (A:Type)(eqA:A->A->Prop)(st:Equivalence  eqA)
   (f:key->elt->A->A)(i:A),
   Proper (E.eq==>eq==>eqA==>eqA) f ->
   Equal m1 m2 ->
   eqA (fold f m1 i) (fold f m2 i).
  Proof.
  intros m1 m2 A eqA st f i Hf Heq.
  rewrite 2 fold_spec_right.
  apply fold_right_eqlistA with (eqA:=eqke) (eqB:=eqA); auto.
  intros (k,e) (k',e') (Hk,He) a a' Ha; simpl in *; apply Hf; auto.
  apply eqlistA_rev. apply elements_Equal_eqlistA. auto.
  Qed.

  Lemma fold_Add_Above : forall m1 m2 x e (A:Type)(eqA:A->A->Prop)(st:Equivalence eqA)
   (f:key->elt->A->A)(i:A) (P:Proper (E.eq==>eq==>eqA==>eqA) f),
   Above x m1 -> Add x e m1 m2 ->
   eqA (fold f m2 i) (f x e (fold f m1 i)).
  Proof.
  intros. rewrite 2 fold_spec_right. set (f':=uncurry f).
  transitivity (fold_right f' i (rev (elements m1 ++ (x,e)::nil))).
  apply fold_right_eqlistA with (eqA:=eqke) (eqB:=eqA); auto.
  intros (k1,e1) (k2,e2) (Hk,He) a1 a2 Ha; unfold f'; simpl in *. apply P; auto.
  apply eqlistA_rev.
  apply elements_Add_Above; auto.
  rewrite distr_rev; simpl.
  reflexivity.
  Qed.

  Lemma fold_Add_Below : forall m1 m2 x e (A:Type)(eqA:A->A->Prop)(st:Equivalence eqA)
   (f:key->elt->A->A)(i:A) (P:Proper (E.eq==>eq==>eqA==>eqA) f),
   Below x m1 -> Add x e m1 m2 ->
   eqA (fold f m2 i) (fold f m1 (f x e i)).
  Proof.
  intros. rewrite 2 fold_spec_right. set (f':=uncurry f).
  transitivity (fold_right f' i (rev (((x,e)::nil)++elements m1))).
  apply fold_right_eqlistA with (eqA:=eqke) (eqB:=eqA); auto.
  intros (k1,e1) (k2,e2) (Hk,He) a1 a2 Ha; unfold f'; simpl in *; apply P; auto.
  apply eqlistA_rev.
  simpl; apply elements_Add_Below; auto.
  rewrite distr_rev; simpl.
  rewrite fold_right_app.
  reflexivity.
  Qed.

  End Fold_properties.

 End Elt.

End OrdProperties.

