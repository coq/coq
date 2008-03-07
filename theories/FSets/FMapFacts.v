(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(** * Finite maps library *)

(** This functor derives additional facts from [FMapInterface.S]. These
  facts are mainly the specifications of [FMapInterface.S] written using 
  different styles: equivalence and boolean equalities. 
*)

Require Import Bool DecidableType DecidableTypeEx OrderedType.
Require Export FMapInterface. 
Set Implicit Arguments.
Unset Strict Implicit.

(** * Facts about weak maps *)

Module WFacts (E:DecidableType)(Import M:WSfun E).

Notation eq_dec := E.eq_dec.
Definition eqb x y := if eq_dec x y then true else false.

Lemma eq_bool_alt : forall b b', b=b' <-> (b=true <-> b'=true).
Proof.
 destruct b; destruct b'; intuition.
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
intros.
generalize (find_mapsto_iff m x); destruct (find x m).
split; intros; try discriminate.
destruct H0.
exists e; rewrite H; auto.
split; auto.
intros; intros (e,H1).
rewrite H in H1; discriminate.
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
 exists a, exists y, E.eq y x /\ b = f y a /\ MapsTo x a m.
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
intros.
generalize (find_mapsto_iff m x) (find_mapsto_iff m y) (fun e => MapsTo_iff m e H).
destruct (find x m); destruct (find y m); intros.
rewrite <- H0; rewrite H2; rewrite H1; auto.
symmetry; rewrite <- H1; rewrite <- H2; rewrite H0; auto.
rewrite <- H0; rewrite H2; rewrite H1; auto.
auto.
Qed.

Lemma empty_o : forall x, find x (empty elt) = None.
Proof.
intros.
case_eq (find x (empty elt)); intros; auto.
generalize (find_2 H).
rewrite empty_mapsto_iff; intuition.
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
intros.
case_eq (find y m); intros; auto with map.
case_eq (find y (add x e m)); intros; auto with map.
rewrite <- H0; symmetry.
apply find_1; apply add_3 with x e; auto with map.
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
intros.
generalize (remove_1 (m:=m) H).
generalize (find_mapsto_iff (remove x m) y).
destruct (find y (remove x m)); auto.
destruct 2.
exists e; rewrite H0; auto.
Qed.
Hint Resolve remove_eq_o : map.

Lemma remove_neq_o : forall m x y, 
 ~ E.eq x y -> find y (remove x m) = find y m. 
Proof.
intros.
case_eq (find y m); intros; auto with map.
case_eq (find y (remove x m)); intros; auto with map.
rewrite <- H0; symmetry.
apply find_1; apply remove_3 with x; auto with map.
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

Definition option_map (A B:Type)(f:A->B)(o:option A) : option B := 
 match o with 
  | Some a => Some (f a)
  | None => None
 end.

Lemma map_o : forall m x (f:elt->elt'), 
 find x (map f m) = option_map f (find x m). 
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
 find x (mapi f m) = option_map (f x) (find x m).
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
intros.
assert (forall e, find x m = Some e <-> InA (eq_key_elt (elt:=elt)) (x,e) (elements m)).
 intros; rewrite <- find_mapsto_iff; apply elements_mapsto_iff.
assert (H0:=elements_3w m).
generalize (fun e => @findA_NoDupA _ _ _ E.eq_sym E.eq_trans eq_dec (elements m) x e H0).
fold (eqb x).
destruct (find x m); destruct (findA (eqb x) (elements m)); 
 simpl; auto; intros.
symmetry; rewrite <- H1; rewrite <- H; auto.
symmetry; rewrite <- H1; rewrite <- H; auto.
rewrite H; rewrite H1; auto.
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

(** * Relations between [Equal], [Equiv] and [Equivb]. *)

(** First, [Equal] is [Equiv] with Leibniz on elements. *)

Lemma Equal_Equiv : forall (m m' : t elt), 
  Equal m m' <-> Equiv (@Logic.eq elt) m m'.
Proof.
 unfold Equal, Equiv; split; intros.
 split; intros.
 rewrite in_find_iff, in_find_iff, H; intuition.
 rewrite find_mapsto_iff in H0,H1; congruence.
 destruct H.
 narrow H with y.
 narrow H0 with y.
 do 2 rewrite in_find_iff in H.
 generalize (find_mapsto_iff m y)(find_mapsto_iff m' y).
 do 2 destruct find; auto; intros.
 f_equal; apply H0; [rewrite H1|rewrite H2]; auto.
 destruct H as [H _]; now elim H.
 destruct H as [_ H]; now elim H.
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

Definition Equal_ST : forall elt:Type, Setoid_Theory (t elt) (@Equal _).
Proof. 
constructor; [apply Equal_refl | apply Equal_sym | apply Equal_trans].
Qed.

Add Relation key E.eq 
 reflexivity proved by E.eq_refl 
 symmetry proved by E.eq_sym
 transitivity proved by E.eq_trans 
 as KeySetoid.

Implicit Arguments Equal [[elt]].

Add Relation (t elt) Equal  
 reflexivity proved by (@Equal_refl elt)
 symmetry proved by (@Equal_sym elt)
 transitivity proved by (@Equal_trans elt)
 as EqualSetoid.

Add Morphism (@In elt) with signature E.eq ==> Equal ==> iff as In_m.
Proof.
unfold Equal; intros k k' Hk m m' Hm.
rewrite (In_iff m Hk), in_find_iff, in_find_iff, Hm; intuition.
Qed.

Add Morphism (@MapsTo elt)
 with signature E.eq ==> Logic.eq ==> Equal ==> iff as MapsTo_m.
Proof.
unfold Equal; intros k k' Hk e m m' Hm.
rewrite (MapsTo_iff m e Hk), find_mapsto_iff, find_mapsto_iff, Hm; 
 intuition.
Qed.

Add Morphism (@Empty elt) with signature Equal ==> iff as Empty_m.
Proof.
unfold Empty; intros m m' Hm; intuition.
rewrite <-Hm in H0; eauto.
rewrite Hm in H0; eauto.
Qed.

Add Morphism (@is_empty elt) with signature Equal ==> Logic.eq as is_empty_m.
Proof.
intros m m' Hm.
rewrite eq_bool_alt, <-is_empty_iff, <-is_empty_iff, Hm; intuition.
Qed.

Add Morphism (@mem elt) with signature E.eq ==> Equal ==> Logic.eq as mem_m.
Proof.
intros k k' Hk m m' Hm.
rewrite eq_bool_alt, <- mem_in_iff, <-mem_in_iff, Hk, Hm; intuition.
Qed.

Add Morphism (@find elt) with signature E.eq ==> Equal ==> Logic.eq as find_m.
Proof.
intros k k' Hk m m' Hm.
generalize (find_mapsto_iff m k)(find_mapsto_iff m' k')
 (not_find_in_iff m k)(not_find_in_iff m' k'); 
do 2 destruct find; auto; intros.
rewrite <- H, Hk, Hm, H0; auto.
rewrite <- H1, Hk, Hm, H2; auto.
symmetry; rewrite <- H2, <-Hk, <-Hm, H1; auto.
Qed.

Add Morphism (@add elt) with signature 
 E.eq ==> Logic.eq ==> Equal ==> Equal as add_m.
Proof.
intros k k' Hk e m m' Hm y.
rewrite add_o, add_o; do 2 destruct eq_dec; auto.
elim n; rewrite <-Hk; auto.
elim n; rewrite Hk; auto.
Qed.

Add Morphism (@remove elt) with signature
 E.eq ==> Equal ==> Equal as remove_m.
Proof.
intros k k' Hk m m' Hm y.
rewrite remove_o, remove_o; do 2 destruct eq_dec; auto.
elim n; rewrite <-Hk; auto.
elim n; rewrite Hk; auto.
Qed.

Add Morphism (@map elt elt') with signature Logic.eq ==> Equal ==> Equal as map_m.
Proof.
intros f m m' Hm y.
rewrite map_o, map_o, Hm; auto.
Qed.

(* Later: Add Morphism cardinal *)

(* old name: *)
Notation not_find_mapsto_iff := not_find_in_iff.

End WFacts.

(** * Same facts for full maps *)

Module Facts (M:S). 
 Module D := OT_as_DT M.E.
 Include WFacts D M.
End Facts.

(** * Additional Properties for weak maps 
 
    Results about [fold], [elements], induction principles...
*)

Module WProperties (E:DecidableType)(M:WSfun E).
 Module Import F:=WFacts E M. 
 Import M.

 Section Elt. 
  Variable elt:Type.

  Definition Add x (e:elt) m m' := forall y, find y m' = find y (add x e m).

  Notation eqke := (@eq_key_elt elt).
  Notation eqk := (@eq_key elt).

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

  Lemma fold_Empty : forall m (A:Type)(f:key->elt->A->A)(i:A),
   Empty m -> fold f m i = i.
  Proof.
  intros.
  rewrite fold_1.
  rewrite elements_Empty in H; rewrite H; simpl; auto.
  Qed.

  Lemma NoDupA_eqk_eqke : forall l, NoDupA eqk l -> NoDupA eqke l.
  Proof.
  induction 1; auto.
  constructor; auto.
  contradict H.
  destruct x as (x,y).
  rewrite InA_alt in *; destruct H as ((a,b),((H1,H2),H3)); simpl in *.
  exists (a,b); auto.
  Qed.

  Lemma fold_Equal : forall m1 m2 (A:Type)(eqA:A->A->Prop)(st:Setoid_Theory A eqA)
   (f:key->elt->A->A)(i:A), 
   compat_op eqke eqA (fun y =>f (fst y) (snd y)) -> 
   transpose eqA (fun y => f (fst y) (snd y)) -> 
   Equal m1 m2 -> 
   eqA (fold f m1 i) (fold f m2 i).
  Proof.
  assert (eqke_refl : forall p, eqke p p).
   red; auto.
  assert (eqke_sym : forall p p', eqke p p' -> eqke p' p).
   intros (x1,x2) (y1,y2); unfold eq_key_elt; simpl; intuition.
  assert (eqke_trans : forall p p' p'', eqke p p' -> eqke p' p'' -> eqke p p'').
   intros (x1,x2) (y1,y2) (z1,z2); unfold eq_key_elt; simpl.
   intuition; eauto; congruence.
  intros; do 2 rewrite fold_1; do 2 rewrite <- fold_left_rev_right.
  apply fold_right_equivlistA with (eqA:=eqke) (eqB:=eqA); auto.
  apply NoDupA_rev; auto; apply NoDupA_eqk_eqke; apply elements_3w.
  apply NoDupA_rev; auto; apply NoDupA_eqk_eqke; apply elements_3w.
  red; intros.
  do 2 rewrite InA_rev.
  destruct x; do 2 rewrite <- elements_mapsto_iff.
  do 2 rewrite find_mapsto_iff.
  rewrite H1; split; auto.
  Qed.

  Lemma fold_Add : forall m1 m2 x e (A:Type)(eqA:A->A->Prop)(st:Setoid_Theory A eqA)
   (f:key->elt->A->A)(i:A), 
   compat_op eqke eqA (fun y =>f (fst y) (snd y)) -> 
   transpose eqA (fun y =>f (fst y) (snd y)) -> 
   ~In x m1 -> Add x e m1 m2 -> 
   eqA (fold f m2 i) (f x e (fold f m1 i)).
  Proof.
  assert (eqke_refl : forall p, eqke p p).
   red; auto.
  assert (eqke_sym : forall p p', eqke p p' -> eqke p' p).
   intros (x1,x2) (y1,y2); unfold eq_key_elt; simpl; intuition.
  assert (eqke_trans : forall p p' p'', eqke p p' -> eqke p' p'' -> eqke p p'').
   intros (x1,x2) (y1,y2) (z1,z2); unfold eq_key_elt; simpl.
   intuition; eauto; congruence.
  intros; do 2 rewrite fold_1; do 2 rewrite <- fold_left_rev_right.
  set (f':=fun y x0 => f (fst y) (snd y) x0) in *.
  change (f x e (fold_right f' i (rev (elements m1))))
   with (f' (x,e) (fold_right f' i (rev (elements m1)))).
  apply fold_right_add with (eqA:=eqke)(eqB:=eqA); auto.
  apply NoDupA_rev; auto; apply NoDupA_eqk_eqke; apply elements_3w.
  apply NoDupA_rev; auto; apply NoDupA_eqk_eqke; apply elements_3w.
  rewrite InA_rev.
  contradict H1.
  exists e.
  rewrite elements_mapsto_iff; auto.
  intros a.
  rewrite InA_cons; do 2 rewrite InA_rev; 
  destruct a as (a,b); do 2 rewrite <- elements_mapsto_iff.
  do 2 rewrite find_mapsto_iff; unfold eq_key_elt; simpl.
  rewrite H2.
  rewrite add_o.
  destruct (eq_dec x a); intuition.
  inversion H3; auto.
  f_equal; auto.
  elim H1.
  exists b; apply MapsTo_1 with a; auto with map.
  elim n; auto.
  Qed.

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
  apply fold_Equal with (eqA:=@eq _); auto.
  constructor; auto; congruence.
  red; auto.
  red; auto.
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
  apply fold_Add; auto.
  constructor; intros; auto; congruence.
  red; simpl; auto.
  red; simpl; auto.
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

  Lemma map_induction :
   forall P : t elt -> Type,
   (forall m, Empty m -> P m) ->
   (forall m m', P m -> forall x e, ~In x m -> Add x e m m' -> P m') ->
   forall m, P m.
  Proof.
  intros; remember (cardinal m) as n; revert m Heqn; induction n; intros.
  apply X; apply cardinal_inv_1; auto.

  destruct (cardinal_inv_2 (sym_eq Heqn)) as ((x,e),H0); simpl in *.
  assert (Add x e (remove x m) m).
   red; intros.
   rewrite add_o; rewrite remove_o; destruct (eq_dec x y); eauto with map.
  apply X0 with (remove x m) x e; auto with map.
  apply IHn; auto with map.
  assert (S n = S (cardinal (remove x m))).
   rewrite Heqn; eapply cardinal_2; eauto with map.
  inversion H1; auto with map.
  Qed.

  (** * Let's emulate some functions not present in the interface *)

  Definition filter (f : key -> elt -> bool)(m : t elt) := 
   fold (fun k e m => if f k e then add k e m else m) m (empty _).

  Definition for_all (f : key -> elt -> bool)(m : t elt) := 
   fold (fun k e b => if f k e then b else false) m true.

  Definition exists_ (f : key -> elt -> bool)(m : t elt) := 
   fold (fun k e b => if f k e then true else b) m false.

  Definition partition (f : key -> elt -> bool)(m : t elt) := 
   (filter f m, filter (fun k e => negb (f k e))).

  Section Specs.
  Variable f : key -> elt -> bool.
  Hypothesis Hf : forall e, compat_bool E.eq (fun k => f k e).

  Lemma filter_iff : forall m k e, 
   MapsTo k e (filter f m) <-> MapsTo k e m /\ f k e = true.
  Proof.
  unfold filter; intros.
  rewrite fold_1.
  rewrite <- fold_left_rev_right.
  rewrite (elements_mapsto_iff m).
  rewrite <- (InA_rev eqke (k,e) (elements m)).
  assert (NoDupA eqk (rev (elements m))).
   apply NoDupA_rev; auto; try apply elements_3w; auto.
   intros (k1,e1); compute; auto.
   intros (k1,e1)(k2,e2); compute; auto.
   intros (k1,e1)(k2,e2)(k3,e3); compute; eauto.
  induction (rev (elements m)); simpl; auto.
  
  rewrite empty_mapsto_iff.
  intuition.
  inversion H1.

  destruct a as (k',e'); simpl.
  inversion_clear H.
  case_eq (f k' e'); intros; simpl;
   try rewrite add_mapsto_iff; rewrite IHl; clear IHl; intuition.
  constructor; red; auto.
  rewrite (Hf e' H2),H4 in H; auto.
  inversion_clear H3.
  compute in H2; destruct H2; auto.
  destruct (E.eq_dec k' k); auto.
  elim H0.
  rewrite InA_alt in *; destruct H2 as (w,Hw); exists w; intuition.
  red in H2; red; simpl in *; intuition.
  rewrite e0; auto.
  inversion_clear H3; auto.
  compute in H2; destruct H2.
  rewrite (Hf e H2),H3,H in H4; discriminate.
  Qed.
  
  Lemma for_all_iff : forall m,
   for_all f m = true <-> (forall k e, MapsTo k e m -> f k e = true).
  Proof.
  cut (forall m : t elt,
       for_all f m = true <->
       (forall k e, InA eqke (k,e) (rev (elements m)) -> f k e = true)).
  intros; rewrite H; split; intros.
  apply H0; rewrite InA_rev, <- elements_mapsto_iff; auto.
  apply H0; rewrite InA_rev, <- elements_mapsto_iff in H1; auto.

  unfold for_all; intros.
  rewrite fold_1.
  rewrite <- fold_left_rev_right.
  assert (NoDupA eqk (rev (elements m))).
   apply NoDupA_rev; auto; try apply elements_3w; auto.
   intros (k1,e1); compute; auto.
   intros (k1,e1)(k2,e2); compute; auto.
   intros (k1,e1)(k2,e2)(k3,e3); compute; eauto.
  induction (rev (elements m)); simpl; auto.
  
  intuition.
  inversion H1.

  destruct a as (k,e); simpl.
  inversion_clear H.
  case_eq (f k e); intros; simpl;
   try rewrite IHl; clear IHl; intuition.
  inversion_clear H3; auto.
  compute in H4; destruct H4.
  rewrite (Hf e0 H3), H4; auto.
  rewrite <-H, <-(H2 k e); auto.
  constructor; red; auto.
  Qed.
  
  Lemma exists_iff : forall m,
   exists_ f m = true <-> 
   (exists p, MapsTo (fst p) (snd p) m /\ f (fst p) (snd p) = true).
  Proof.
  cut (forall m : t elt,
       exists_ f m = true <->
       (exists p, InA eqke p (rev (elements m)) 
         /\ f (fst p) (snd p) = true)).
  intros; rewrite H; split; intros.
  destruct H0 as ((k,e),Hke); exists (k,e).
  rewrite InA_rev, <-elements_mapsto_iff in Hke; auto.
  destruct H0 as ((k,e),Hke); exists (k,e).
  rewrite InA_rev, <-elements_mapsto_iff; auto.
  unfold exists_; intros.
  rewrite fold_1.
  rewrite <- fold_left_rev_right.
  assert (NoDupA eqk (rev (elements m))).
   apply NoDupA_rev; auto; try apply elements_3w; auto.
   intros (k1,e1); compute; auto.
   intros (k1,e1)(k2,e2); compute; auto.
   intros (k1,e1)(k2,e2)(k3,e3); compute; eauto.
  induction (rev (elements m)); simpl; auto.
  
  intuition; try discriminate.
  destruct H0 as ((k,e),(Hke,_)); inversion Hke.

  destruct a as (k,e); simpl.
  inversion_clear H.
  case_eq (f k e); intros; simpl;
   try rewrite IHl; clear IHl; intuition.
  exists (k,e); simpl; split; auto.
  constructor; red; auto.
  destruct H2 as ((k',e'),(Hke',Hf')); exists (k',e'); simpl; auto.
  destruct H2 as ((k',e'),(Hke',Hf')); simpl in *.
  inversion_clear Hke'.
  compute in H2; destruct H2.
  rewrite (Hf e' H2), H3,H in Hf'; discriminate.
  exists (k',e'); auto.
  Qed.
  End Specs.

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

 Add Morphism (@cardinal elt) with signature Equal ==> Logic.eq as cardinal_m.
 Proof. intros; apply Equal_cardinal; auto. Qed.

End WProperties.

(** * Same Properties for full maps *)

Module Properties (M:S). 
 Module D := OT_as_DT M.E.
 Include WProperties D M.
End Properties.

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
  apply SortA_equivlistA_eqlistA; eauto; 
  unfold O.eqke, O.ltk; simpl; intuition; eauto.
  Qed.

  Ltac clean_eauto := unfold O.eqke, O.ltk; simpl; intuition; eauto.

  Definition gtb (p p':key*elt) := match E.compare (fst p) (fst p') with GT _ => true | _ => false end.
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

  Lemma gtb_compat : forall p, compat_bool eqke (gtb p).
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

  Lemma leb_compat : forall p, compat_bool eqke (leb p).
  Proof.
   red; intros x a b H.
   unfold leb; f_equal; apply gtb_compat; auto.
  Qed.

  Hint Resolve gtb_compat leb_compat elements_3 : map.

  Lemma elements_split : forall p m, 
    elements m = elements_lt p m ++ elements_ge p m.
  Proof.
  unfold elements_lt, elements_ge, leb; intros.
  apply filter_split with (eqA:=eqk) (ltA:=ltk); eauto with map.
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
  apply sort_equivlistA_eqlistA; auto with map.
  apply (@SortA_app _ eqke); auto with map.
  apply (@filter_sort _ eqke); auto with map; clean_eauto.
  constructor; auto with map.
  apply (@filter_sort _ eqke); auto with map; clean_eauto.
  rewrite (@InfA_alt _ eqke); auto with map; try (clean_eauto; fail).
  intros.
  rewrite filter_InA in H1; auto with map; destruct H1.
  rewrite leb_1 in H2.
  destruct y; unfold O.ltk in *; simpl in *.
  rewrite <- elements_mapsto_iff in H1.
  assert (~E.eq x t0).
   contradict H.
   exists e0; apply MapsTo_1 with t0; auto.
  ME.order.
  apply (@filter_sort _ eqke); auto with map; clean_eauto.
  intros.
  rewrite filter_InA in H1; auto with map; destruct H1.
  rewrite gtb_1 in H3.
  destruct y; destruct x0; unfold O.ltk in *; simpl in *.
  inversion_clear H2.
  red in H4; simpl in *; destruct H4.
  ME.order.
  rewrite filter_InA in H4; auto with map; destruct H4.
  rewrite leb_1 in H4.
  unfold O.ltk in *; simpl in *; ME.order.
  red; intros a; destruct a.
  rewrite InA_app_iff; rewrite InA_cons.
  do 2 (rewrite filter_InA; auto with map).
  do 2 rewrite <- elements_mapsto_iff.
  rewrite leb_1; rewrite gtb_1.
  rewrite find_mapsto_iff; rewrite (H0 t0); rewrite <- find_mapsto_iff.
  rewrite add_mapsto_iff.
  unfold O.eqke, O.ltk; simpl.
  destruct (E.compare t0 x); intuition.
  right; split; auto; ME.order.
  ME.order.
  elim H.
  exists e0; apply MapsTo_1 with t0; auto.
  right; right; split; auto; ME.order.
  ME.order.
  right; split; auto; ME.order.
  Qed.

  Lemma elements_Add_Above : forall m m' x e, 
   Above x m -> Add x e m m' -> 
     eqlistA eqke (elements m') (elements m ++ (x,e)::nil).
  Proof.
  intros.
  apply sort_equivlistA_eqlistA; auto with map.
  apply (@SortA_app _ eqke); auto with map.
  intros.
  inversion_clear H2.
  destruct x0; destruct y.
  rewrite <- elements_mapsto_iff in H1.
  unfold O.eqke, O.ltk in *; simpl in *; destruct H3.
  apply ME.lt_eq with x; auto.
  apply H; firstorder.
  inversion H3.
  red; intros a; destruct a.
  rewrite InA_app_iff; rewrite InA_cons; rewrite InA_nil.
  do 2 rewrite <- elements_mapsto_iff.
  rewrite find_mapsto_iff; rewrite (H0 t0); rewrite <- find_mapsto_iff.
  rewrite add_mapsto_iff; unfold O.eqke; simpl.
  intuition.
  destruct (ME.eq_dec x t0); auto.
  elimtype False.
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
  apply sort_equivlistA_eqlistA; auto with map.
  change (sort ltk (((x,e)::nil) ++ elements m)).
  apply (@SortA_app _ eqke); auto with map.
  intros.
  inversion_clear H1.
  destruct y; destruct x0.
  rewrite <- elements_mapsto_iff in H2.
  unfold O.eqke, O.ltk in *; simpl in *; destruct H3.
  apply ME.eq_lt with x; auto.
  apply H; firstorder.
  inversion H3.
  red; intros a; destruct a.
  rewrite InA_cons.
  do 2 rewrite <- elements_mapsto_iff.
  rewrite find_mapsto_iff; rewrite (H0 t0); rewrite <- find_mapsto_iff.
  rewrite add_mapsto_iff; unfold O.eqke; simpl.
  intuition.
  destruct (ME.eq_dec x t0); auto.
  elimtype False.
  assert (In t0 m).
   exists e0; auto.
  generalize (H t0 H1).
  ME.order.
  Qed.

  Lemma elements_Equal_eqlistA : forall (m m': t elt), 
   Equal m m' -> eqlistA eqke (elements m) (elements m').
  Proof.
  intros.
  apply sort_equivlistA_eqlistA; auto with map.
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
  injection H; clear H; intros; subst.
  inversion_clear H1.
  red in H; simpl in *; intuition.
  elim H0; eauto.
  inversion H.
  change (max_elt_aux (p::l) = Some (x,e)) in H.
  generalize (IHl x e H); clear IHl; intros IHl.
  inversion_clear H1; [ | inversion_clear H2; eauto ].
  red in H3; simpl in H3; destruct H3.
  destruct p as (p1,p2).
  destruct (ME.eq_dec p1 x).
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
  destruct p; injection H; intros; subst.
  inversion_clear H1.
  red in H2; destruct H2; simpl in *; ME.order.
  inversion_clear H4.
  rewrite (@InfA_alt _ eqke) in H3; eauto.
  apply (H3 (y,x0)); auto.
  unfold lt_key; simpl; intuition; eauto.
  intros (x1,x2) (y1,y2) (z1,z2); compute; intuition; eauto.
  intros (x1,x2) (y1,y2) (z1,z2); compute; intuition; eauto.
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
      but with one additionnal hypothesis (some [transpose] fact). *)

  Lemma fold_Equal : forall s1 s2 (A:Type)(eqA:A->A->Prop)(st:Setoid_Theory A eqA)
   (f:key->elt->A->A)(i:A), 
   compat_op eqke eqA (fun y =>f (fst y) (snd y)) -> 
   Equal s1 s2 -> 
   eqA (fold f s1 i) (fold f s2 i).
  Proof.
  intros.
  do 2 rewrite fold_1.
  do 2 rewrite <- fold_left_rev_right.
  apply fold_right_eqlistA with (eqA:=eqke) (eqB:=eqA); auto.
  apply eqlistA_rev.
  apply elements_Equal_eqlistA; auto.
  Qed.

  Lemma fold_Add : forall s1 s2 x e (A:Type)(eqA:A->A->Prop)(st:Setoid_Theory A eqA)
   (f:key->elt->A->A)(i:A), 
   compat_op eqke eqA (fun y =>f (fst y) (snd y)) -> 
   transpose eqA (fun y =>f (fst y) (snd y)) -> 
   ~In x s1 -> Add x e s1 s2 -> 
   eqA (fold f s2 i) (f x e (fold f s1 i)).
  Proof.
  intros; do 2 rewrite fold_1; do 2 rewrite <- fold_left_rev_right.
  set (f':=fun y x0 => f (fst y) (snd y) x0) in *.
  change (f x e (fold_right f' i (rev (elements s1))))
   with (f' (x,e) (fold_right f' i (rev (elements s1)))).
  trans_st (fold_right f' i 
              (rev (elements_lt (x, e) s1 ++ (x,e) :: elements_ge (x, e) s1))).
  apply fold_right_eqlistA with (eqA:=eqke) (eqB:=eqA); auto.
  apply eqlistA_rev.
  apply elements_Add; auto.
  rewrite distr_rev; simpl.
  rewrite app_ass; simpl.
  rewrite (elements_split (x,e) s1).
  rewrite distr_rev; simpl.
  apply fold_right_commutes with (eqA:=eqke) (eqB:=eqA); auto.
  Qed.

  Lemma fold_Add_Above : forall s1 s2 x e (A:Type)(eqA:A->A->Prop)(st:Setoid_Theory A eqA)
   (f:key->elt->A->A)(i:A), 
   compat_op eqke eqA (fun y =>f (fst y) (snd y)) -> 
   Above x s1 -> Add x e s1 s2 -> 
   eqA (fold f s2 i) (f x e (fold f s1 i)).
  Proof.
  intros; do 2 rewrite fold_1; do 2 rewrite <- fold_left_rev_right.
  set (f':=fun y x0 => f (fst y) (snd y) x0) in *.
  trans_st (fold_right f' i (rev (elements s1 ++ (x,e)::nil))).
  apply fold_right_eqlistA with (eqA:=eqke) (eqB:=eqA); auto.
  apply eqlistA_rev.
  apply elements_Add_Above; auto.
  rewrite distr_rev; simpl.
  refl_st.
  Qed.

  Lemma fold_Add_Below : forall s1 s2 x e (A:Type)(eqA:A->A->Prop)(st:Setoid_Theory A eqA)
   (f:key->elt->A->A)(i:A), 
   compat_op eqke eqA (fun y =>f (fst y) (snd y)) -> 
   Below x s1 -> Add x e s1 s2 -> 
   eqA (fold f s2 i) (fold f s1 (f x e i)).
  Proof.
  intros; do 2 rewrite fold_1; do 2 rewrite <- fold_left_rev_right.
  set (f':=fun y x0 => f (fst y) (snd y) x0) in *.
  trans_st (fold_right f' i (rev (((x,e)::nil)++elements s1))).
  apply fold_right_eqlistA with (eqA:=eqke) (eqB:=eqA); auto.
  apply eqlistA_rev.
  simpl; apply elements_Add_Below; auto.
  rewrite distr_rev; simpl.
  rewrite fold_right_app.
  refl_st.
  Qed.

  End Fold_properties.

 End Elt.

End OrdProperties.





