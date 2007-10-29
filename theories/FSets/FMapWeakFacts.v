(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(** * Finite maps library *)

(** This functor derives additional facts from [FMapWeakInterface.S]. These
  facts are mainly the specifications of [FMapWeakInterface.S] written using 
  different styles: equivalence and boolean equalities. 
*)

Require Import Bool.
Require Import OrderedType.
Require Export FMapWeakInterface. 
Set Implicit Arguments.
Unset Strict Implicit.

Module Facts (M:S)(D:DecidableType with Definition t:=M.E.t 
                                   with Definition eq:=M.E.eq).
Import M.

Notation eq_dec := D.eq_dec.
Definition eqb x y := if eq_dec x y then true else false.

Lemma MapsTo_fun : forall (elt:Set) m x (e e':elt), 
  MapsTo x e m -> MapsTo x e' m -> e=e'.
Proof.
intros.
generalize (find_1 H) (find_1 H0); clear H H0.
intros; rewrite H in H0; injection H0; auto.
Qed.

(** * Specifications written using equivalences *)

Section IffSpec. 
Variable elt elt' elt'': Set.
Implicit Type m: t elt.
Implicit Type x y z: key.
Implicit Type e: elt.

Lemma MapsTo_iff : forall m x y e, E.eq x y -> (MapsTo x e m <-> MapsTo y e m).
Proof.
split; apply MapsTo_1; auto.
Qed.

Lemma In_iff : forall m x y, E.eq x y -> (In x m <-> In y m).
Proof.
unfold In.
split; intros (e0,H0); exists e0.
apply (MapsTo_1 H H0); auto.
apply (MapsTo_1 (E.eq_sym H) H0); auto.
Qed.

Lemma find_mapsto_iff : forall m x e, MapsTo x e m <-> find x m = Some e.
Proof.
split; [apply find_1|apply find_2].
Qed.

Lemma not_find_mapsto_iff : forall m x, ~In x m <-> find x m = None.
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

Lemma mem_in_iff : forall m x, In x m <-> mem x m = true.
Proof.
split; [apply mem_1|apply mem_2].
Qed.

Lemma not_mem_in_iff : forall m x, ~In x m <-> mem x m = false.
Proof.
intros; rewrite mem_in_iff; destruct (mem x m); intuition.
Qed.

Lemma equal_iff : forall m m' cmp, Equal cmp m m' <-> equal cmp m m' = true.
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

(* Unfortunately, we don't have simple equivalences for [mapi] 
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

(**  * Specifications written using boolean predicates *)

Section BoolSpec.

Lemma mem_find_b : forall (elt:Set)(m:t elt)(x:key), mem x m = if find x m then true else false. 
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

Variable elt elt' elt'' : Set.
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

Definition option_map (A:Set)(B:Set)(f:A->B)(o:option A) : option B := 
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
assert (NoDupA (eq_key (elt:=elt)) (elements m)). 
 exact (elements_3w m).
generalize (fun e => @findA_NoDupA _ _ _ D.eq_sym D.eq_trans eq_dec (elements m) x e H0).
unfold eqb.
destruct (find x m); destruct (findA (fun y:D.t => if eq_dec x y then true else false) (elements m)); 
 simpl; auto; intros.
symmetry; rewrite <- H1; rewrite <- H; auto.
symmetry; rewrite <- H1; rewrite <- H; auto.
rewrite H; rewrite H1; auto.
Qed.

Lemma elements_b : forall m x, mem x m = existsb (fun p => eqb x (fst p)) (elements m).
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

End Facts.


Module Properties 
 (M:S)(D:DecidableType with Definition t:=M.E.t 
                       with Definition eq:=M.E.eq).
 Module F:=Facts M D. 
 Import F.
 Import M.

 Section Elt. 
  Variable elt:Set.

  Definition cardinal (m:t elt) := length (elements m).

  Definition Equal (m m':t elt) := forall y, find y m = find y m'.
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

  Lemma fold_Empty : forall m (A:Set)(f:key->elt->A->A)(i:A),
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
  swap H.
  destruct x as (x,y).
  rewrite InA_alt in *; destruct H1 as ((a,b),((H1,H2),H3)); simpl in *.
  exists (a,b); auto.
  Qed.

  Lemma fold_Equal : forall m1 m2 (A:Set)(eqA:A->A->Prop)(st:Setoid_Theory A eqA)
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

  Lemma fold_Add : forall m1 m2 x e (A:Set)(eqA:A->A->Prop)(st:Setoid_Theory A eqA)
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
  swap H1.
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

  Lemma cardinal_fold : forall m, cardinal m = fold (fun _ _ => S) m 0.
  Proof.
  intros; unfold cardinal; rewrite fold_1.
  symmetry; apply fold_left_length; auto.
  Qed.
 
  Lemma Equal_cardinal : forall m m', Equal m m' -> cardinal m = cardinal m'.
  Proof.
  intros; do 2 rewrite cardinal_fold.
  apply fold_Equal with (eqA:=@eq _); auto.
  constructor; auto; congruence.
  red; auto.
  red; auto.
  Qed.

  Lemma cardinal_1 : forall m, Empty m -> cardinal m = 0.
  Proof.
  intros; unfold cardinal; rewrite elements_Empty in H; rewrite H; simpl; auto.
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

  Lemma cardinal_inv_1 : forall m, cardinal m = 0 -> Empty m. 
  Proof. 
  unfold cardinal; intros m H a e.
  rewrite elements_mapsto_iff.    
  destruct (elements m); simpl in *.
  red; inversion 1.
  inversion H.
  Qed.
  Hint Resolve cardinal_inv_1 : map.

  Lemma cardinal_inv_2 :
   forall m n, cardinal m = S n -> { p : key*elt | MapsTo (fst p) (snd p) m }.
  Proof. 
  unfold cardinal; intros.
  generalize (elements_mapsto_iff m).
  destruct (elements m); try discriminate. 
  exists p; auto.
  rewrite H0; destruct p; simpl; auto.
  constructor; red; auto.
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

 End Elt.

End Properties.

