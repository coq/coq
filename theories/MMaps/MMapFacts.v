(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** * Finite maps library *)

(** This functor derives additional facts from [MMapInterface.S]. These
  facts are mainly the specifications of [MMapInterface.S] written using
  different styles: equivalence and boolean equalities.
*)

Require Import Bool Equalities Orders OrdersFacts OrdersLists.
Require Import Morphisms Permutation SetoidPermutation.
Require Export MMapInterface.
Set Implicit Arguments.
Unset Strict Implicit.

Lemma eq_bool_alt b b' : b=b' <-> (b=true <-> b'=true).
Proof.
 destruct b, b'; intuition.
Qed.

Lemma eq_option_alt {elt}(o o':option elt) :
 o=o' <-> (forall e, o=Some e <-> o'=Some e).
Proof.
split; intros.
- now subst.
- destruct o, o'; rewrite ?H; auto.
  symmetry; now apply H.
Qed.

Lemma option_map_some {A B}(f:A->B) o :
 option_map f o <> None <-> o <> None.
Proof.
 destruct o; simpl. now split. split; now destruct 1.
Qed.

(** * Properties about weak maps *)

Module WProperties_fun (E:DecidableType)(Import M:WSfun E).

Definition Empty {elt}(m : t elt) := forall x e, ~MapsTo x e m.

(** A few things about E.eq *)

Lemma eq_refl x : E.eq x x. Proof. apply E.eq_equiv. Qed.
Lemma eq_sym x y : E.eq x y -> E.eq y x. Proof. apply E.eq_equiv. Qed.
Lemma eq_trans x y z : E.eq x y -> E.eq y z -> E.eq x z.
Proof. apply E.eq_equiv. Qed.
Hint Immediate eq_refl eq_sym : map.
Hint Resolve eq_trans eq_equivalence E.eq_equiv : map.

Definition eqb x y := if E.eq_dec x y then true else false.

Lemma eqb_eq x y : eqb x y = true <-> E.eq x y.
Proof.
 unfold eqb; case E.eq_dec; now intuition.
Qed.

Lemma eqb_sym x y : eqb x y = eqb y x.
Proof.
 apply eq_bool_alt. rewrite !eqb_eq. split; apply E.eq_equiv.
Qed.

(** Initial results about MapsTo and In *)

Lemma mapsto_fun {elt} m x (e e':elt) :
  MapsTo x e m -> MapsTo x e' m -> e=e'.
Proof.
rewrite <- !find_spec. congruence.
Qed.

Lemma in_find {elt} (m : t elt) x : In x m <-> find x m <> None.
Proof.
 unfold In. split.
 - intros (e,H). rewrite <-find_spec in H. congruence.
 - destruct (find x m) as [e|] eqn:H.
   + exists e. now apply find_spec.
   + now destruct 1.
Qed.

Lemma not_in_find {elt} (m : t elt) x : ~In x m <-> find x m = None.
Proof.
 rewrite in_find. split; auto.
 intros; destruct (find x m); trivial. now destruct H.
Qed.

Notation in_find_iff := in_find (only parsing).
Notation not_find_in_iff := not_in_find (only parsing).

(** * [Equal] is a setoid equality. *)

Infix "==" := Equal (at level 30).

Lemma Equal_refl {elt} (m : t elt) : m == m.
Proof. red; reflexivity. Qed.

Lemma Equal_sym {elt} (m m' : t elt) : m == m' -> m' == m.
Proof. unfold Equal; auto. Qed.

Lemma Equal_trans {elt} (m m' m'' : t elt) :
 m == m' -> m' == m'' -> m == m''.
Proof. unfold Equal; congruence. Qed.

Instance Equal_equiv {elt} : Equivalence (@Equal elt).
Proof.
constructor; [exact Equal_refl | exact Equal_sym | exact Equal_trans].
Qed.

Arguments Equal {elt} m m'.

Instance MapsTo_m {elt} :
  Proper (E.eq==>Logic.eq==>Equal==>iff) (@MapsTo elt).
Proof.
intros k k' Hk e e' <- m m' Hm. rewrite <- Hk.
now rewrite <- !find_spec, Hm.
Qed.

Instance In_m {elt} :
  Proper (E.eq==>Equal==>iff) (@In elt).
Proof.
intros k k' Hk m m' Hm. unfold In.
split; intros (e,H); exists e; revert H;
 now rewrite Hk, <- !find_spec, Hm.
Qed.

Instance find_m {elt} : Proper (E.eq==>Equal==>Logic.eq) (@find elt).
Proof.
intros k k' Hk m m' <-.
rewrite eq_option_alt. intros. now rewrite !find_spec, Hk.
Qed.

Instance mem_m {elt} : Proper (E.eq==>Equal==>Logic.eq) (@mem elt).
Proof.
intros k k' Hk m m' Hm. now rewrite eq_bool_alt, !mem_spec, Hk, Hm.
Qed.

Instance Empty_m {elt} : Proper (Equal==>iff) (@Empty elt).
Proof.
intros m m' Hm. unfold Empty. now setoid_rewrite Hm.
Qed.

Instance is_empty_m {elt} : Proper (Equal ==> Logic.eq) (@is_empty elt).
Proof.
intros m m' Hm. rewrite eq_bool_alt, !is_empty_spec.
 now setoid_rewrite Hm.
Qed.

Instance add_m {elt} : Proper (E.eq==>Logic.eq==>Equal==>Equal) (@add elt).
Proof.
intros k k' Hk e e' <- m m' Hm y.
destruct (E.eq_dec k y) as [H|H].
- rewrite <-H, add_spec1. now rewrite Hk, add_spec1.
- rewrite !add_spec2; trivial. now rewrite <- Hk.
Qed.

Instance remove_m {elt} : Proper (E.eq==>Equal==>Equal) (@remove elt).
Proof.
intros k k' Hk m m' Hm y.
destruct (E.eq_dec k y) as [H|H].
- rewrite <-H, remove_spec1. now rewrite Hk, remove_spec1.
- rewrite !remove_spec2; trivial. now rewrite <- Hk.
Qed.

Instance map_m {elt elt'} :
  Proper ((Logic.eq==>Logic.eq)==>Equal==>Equal) (@map elt elt').
Proof.
intros f f' Hf m m' Hm y. rewrite !map_spec, Hm.
destruct (find y m'); simpl; trivial. f_equal. now apply Hf.
Qed.

Instance mapi_m {elt elt'} :
  Proper ((E.eq==>Logic.eq==>Logic.eq)==>Equal==>Equal) (@mapi elt elt').
Proof.
intros f f' Hf m m' Hm y.
destruct (mapi_spec f m y) as (x,(Hx,->)).
destruct (mapi_spec f' m' y) as (x',(Hx',->)).
rewrite <- Hm. destruct (find y m); trivial. simpl.
f_equal. apply Hf; trivial. now rewrite Hx, Hx'.
Qed.

Instance merge_m {elt elt' elt''} :
 Proper ((E.eq==>Logic.eq==>Logic.eq==>Logic.eq)==>Equal==>Equal==>Equal)
  (@merge elt elt' elt'').
Proof.
intros f f' Hf m1 m1' Hm1 m2 m2' Hm2 y.
destruct (find y m1) as [e1|] eqn:H1.
- apply find_spec in H1.
  assert (H : In y m1 \/ In y m2) by (left; now exists e1).
  destruct (merge_spec1 f H) as (y1,(Hy1,->)).
  rewrite Hm1,Hm2 in H.
  destruct (merge_spec1 f' H) as (y2,(Hy2,->)).
  rewrite <- Hm1, <- Hm2. apply Hf; trivial. now transitivity y.
- destruct (find y m2) as [e2|] eqn:H2.
  + apply find_spec in H2.
    assert (H : In y m1 \/ In y m2) by (right; now exists e2).
    destruct (merge_spec1 f H) as (y1,(Hy1,->)).
    rewrite Hm1,Hm2 in H.
    destruct (merge_spec1 f' H) as (y2,(Hy2,->)).
    rewrite <- Hm1, <- Hm2. apply Hf; trivial. now transitivity y.
  + apply not_in_find in H1. apply not_in_find in H2.
    assert (H : ~In y (merge f m1 m2)).
    { intro H. apply merge_spec2 in H. intuition. }
    apply not_in_find in H. rewrite H.
    symmetry. apply not_in_find. intro H'.
    apply merge_spec2 in H'. rewrite <- Hm1, <- Hm2 in H'.
    intuition.
Qed.

(* Later: compatibility for cardinal, fold, ... *)

(** ** Earlier specifications (cf. FMaps) *)

Section OldSpecs.
Variable elt: Type.
Implicit Type m: t elt.
Implicit Type x y z: key.
Implicit Type e: elt.

Lemma MapsTo_1 m x y e : E.eq x y -> MapsTo x e m -> MapsTo y e m.
Proof.
 now intros ->.
Qed.

Lemma find_1 m x e : MapsTo x e m -> find x m = Some e.
Proof. apply find_spec. Qed.

Lemma find_2 m x e : find x m = Some e -> MapsTo x e m.
Proof. apply find_spec. Qed.

Lemma mem_1 m x : In x m -> mem x m = true.
Proof. apply mem_spec. Qed.

Lemma mem_2 m x : mem x m = true -> In x m.
Proof. apply mem_spec. Qed.

Lemma empty_1 : Empty (@empty elt).
Proof.
 intros x e. now rewrite <- find_spec, empty_spec.
Qed.

Lemma is_empty_1 m : Empty m -> is_empty m = true.
Proof.
 unfold Empty; rewrite is_empty_spec. setoid_rewrite <- find_spec.
 intros H x. specialize (H x).
 destruct (find x m) as [e|]; trivial.
 now destruct (H e).
Qed.

Lemma is_empty_2 m : is_empty m = true -> Empty m.
Proof.
 rewrite is_empty_spec. intros H x e. now rewrite <- find_spec, H.
Qed.

Lemma add_1 m x y e : E.eq x y -> MapsTo y e (add x e m).
Proof.
 intros <-. rewrite <-find_spec. apply add_spec1.
Qed.

Lemma add_2 m x y e e' :
  ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
Proof.
 intro. now rewrite <- !find_spec, add_spec2.
Qed.

Lemma add_3 m x y e e' :
  ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
Proof.
 intro. rewrite <- !find_spec, add_spec2; trivial.
Qed.

Lemma remove_1 m x y : E.eq x y -> ~ In y (remove x m).
Proof.
 intros <-. apply not_in_find. apply remove_spec1.
Qed.

Lemma remove_2 m x y e :
  ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
Proof.
 intro. now rewrite <- !find_spec, remove_spec2.
Qed.

Lemma remove_3bis m x y e :
  find y (remove x m) = Some e -> find y m = Some e.
Proof.
 destruct (E.eq_dec x y) as [<-|H].
 - now rewrite remove_spec1.
 - now rewrite remove_spec2.
Qed.

Lemma remove_3 m x y e : MapsTo y e (remove x m) -> MapsTo y e m.
Proof.
 rewrite <-!find_spec. apply remove_3bis.
Qed.

Lemma bindings_1 m x e :
  MapsTo x e m -> InA eq_key_elt (x,e) (bindings m).
Proof. apply bindings_spec1. Qed.

Lemma bindings_2 m x e :
  InA eq_key_elt (x,e) (bindings m) -> MapsTo x e m.
Proof. apply bindings_spec1. Qed.

Lemma bindings_3w m : NoDupA eq_key (bindings m).
Proof. apply bindings_spec2w. Qed.

Lemma cardinal_1 m : cardinal m = length (bindings m).
Proof. apply cardinal_spec. Qed.

Lemma fold_1 m (A : Type) (i : A) (f : key -> elt -> A -> A) :
  fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
Proof. apply fold_spec. Qed.

Lemma equal_1 m m' cmp : Equivb cmp m m' -> equal cmp m m' = true.
Proof. apply equal_spec. Qed.

Lemma equal_2 m m' cmp : equal cmp m m' = true -> Equivb cmp m m'.
Proof. apply equal_spec. Qed.

End OldSpecs.

Lemma map_1 {elt elt'}(m: t elt)(x:key)(e:elt)(f:elt->elt') :
  MapsTo x e m -> MapsTo x (f e) (map f m).
Proof.
 rewrite <- !find_spec, map_spec. now intros ->.
Qed.

Lemma map_2 {elt elt'}(m: t elt)(x:key)(f:elt->elt') :
  In x (map f m) -> In x m.
Proof.
 rewrite !in_find, map_spec. apply option_map_some.
Qed.

Lemma mapi_1 {elt elt'}(m: t elt)(x:key)(e:elt)(f:key->elt->elt') :
  MapsTo x e m ->
  exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
Proof.
 destruct (mapi_spec f m x) as (y,(Hy,Eq)).
 intro H. exists y; split; trivial.
 rewrite <-find_spec in *. now rewrite Eq, H.
Qed.

Lemma mapi_2 {elt elt'}(m: t elt)(x:key)(f:key->elt->elt') :
  In x (mapi f m) -> In x m.
Proof.
 destruct (mapi_spec f m x) as (y,(Hy,Eq)).
 rewrite !in_find. intro H; contradict H. now rewrite Eq, H.
Qed.

(** The ancestor [map2] of the current [merge] was dealing with functions
    on datas only, not on keys. *)

Definition map2 {elt elt' elt''} (f:option elt->option elt'->option elt'')
 := merge (fun _ => f).

Lemma map2_1 {elt elt' elt''}(m: t elt)(m': t elt')
      (x:key)(f:option elt->option elt'->option elt'') :
  In x m \/ In x m' ->
  find x (map2 f m m') = f (find x m) (find x m').
Proof.
 intros. unfold map2.
 now destruct (merge_spec1 (fun _ => f) H) as (y,(_,->)).
Qed.

Lemma map2_2 {elt elt' elt''}(m: t elt)(m': t elt')
      (x:key)(f:option elt->option elt'->option elt'') :
  In x (map2 f m m') -> In x m \/ In x m'.
Proof. apply merge_spec2. Qed.

Hint Immediate MapsTo_1 mem_2 is_empty_2
     map_2 mapi_2 add_3 remove_3 find_2 : map.
Hint Resolve mem_1 is_empty_1 is_empty_2 add_1 add_2 remove_1
     remove_2 find_1 fold_1 map_1 mapi_1 mapi_2 : map.

(** ** Specifications written using equivalences *)

Section IffSpec.
Variable elt: Type.
Implicit Type m: t elt.
Implicit Type x y z: key.
Implicit Type e: elt.

Lemma in_iff m x y : E.eq x y -> (In x m <-> In y m).
Proof. now intros ->. Qed.

Lemma mapsto_iff m x y e : E.eq x y -> (MapsTo x e m <-> MapsTo y e m).
Proof. now intros ->. Qed.

Lemma mem_in_iff m x : In x m <-> mem x m = true.
Proof. symmetry. apply mem_spec. Qed.

Lemma not_mem_in_iff m x : ~In x m <-> mem x m = false.
Proof.
rewrite mem_in_iff; destruct (mem x m); intuition.
Qed.

Lemma mem_find m x : mem x m = true <-> find x m <> None.
Proof.
 rewrite <- mem_in_iff. apply in_find.
Qed.

Lemma not_mem_find m x : mem x m = false <-> find x m = None.
Proof.
 rewrite <- not_mem_in_iff. apply not_in_find.
Qed.

Lemma In_dec m x : { In x m } + { ~ In x m }.
Proof.
 generalize (mem_in_iff m x).
 destruct (mem x m); [left|right]; intuition.
Qed.

Lemma find_mapsto_iff m x e : MapsTo x e m <-> find x m = Some e.
Proof. symmetry. apply find_spec. Qed.

Lemma equal_iff m m' cmp : Equivb cmp m m' <-> equal cmp m m' = true.
Proof. symmetry. apply equal_spec. Qed.

Lemma empty_mapsto_iff x e : MapsTo x e empty <-> False.
Proof.
rewrite <- find_spec, empty_spec. now split.
Qed.

Lemma not_in_empty x : ~In x (@empty elt).
Proof.
intros (e,H). revert H. apply empty_mapsto_iff.
Qed.

Lemma empty_in_iff x : In x (@empty elt) <-> False.
Proof.
split; [ apply not_in_empty | destruct 1 ].
Qed.

Lemma is_empty_iff m : Empty m <-> is_empty m = true.
Proof. split; [apply is_empty_1 | apply is_empty_2 ]. Qed.

Lemma add_mapsto_iff m x y e e' :
  MapsTo y e' (add x e m) <->
     (E.eq x y /\ e=e') \/
     (~E.eq x y /\ MapsTo y e' m).
Proof.
split.
- intros H. destruct (E.eq_dec x y); [left|right]; split; trivial.
  + symmetry. apply (mapsto_fun H); auto with map.
  + now apply add_3 with x e.
- destruct 1 as [(H,H')|(H,H')]; subst; auto with map.
Qed.

Lemma add_mapsto_new m x y e e' : ~In x m ->
  MapsTo y e' (add x e m) <-> (E.eq x y /\ e=e') \/ MapsTo y e' m.
Proof.
 intros.
 rewrite add_mapsto_iff. intuition.
 right; split; trivial. contradict H. exists e'. now rewrite H.
Qed.

Lemma in_add m x y e : In y m -> In y (add x e m).
Proof.
 destruct (E.eq_dec x y) as [<-|H'].
 - now rewrite !in_find, add_spec1.
 - now rewrite !in_find, add_spec2.
Qed.

Lemma add_in_iff m x y e : In y (add x e m) <-> E.eq x y \/ In y m.
Proof.
split.
- intros H. destruct (E.eq_dec x y); [now left|right].
  rewrite in_find, add_spec2 in H; trivial. now apply in_find.
- intros [<-|H].
  + exists e. now apply add_1.
  + now apply in_add.
Qed.

Lemma add_neq_mapsto_iff m x y e e' :
 ~ E.eq x y -> (MapsTo y e' (add x e m) <-> MapsTo y e' m).
Proof.
split; [apply add_3|apply add_2]; auto.
Qed.

Lemma add_neq_in_iff m x y e :
 ~ E.eq x y -> (In y (add x e m)  <-> In y m).
Proof.
split; intros (e',H0); exists e'.
- now apply add_3 with x e.
- now apply add_2.
Qed.

Lemma remove_mapsto_iff m x y e :
  MapsTo y e (remove x m) <-> ~E.eq x y /\ MapsTo y e m.
Proof.
split; [split|destruct 1].
- intro E. revert H. now rewrite <-E, <- find_spec, remove_spec1.
- now apply remove_3 with x.
- now apply remove_2.
Qed.

Lemma remove_in_iff m x y : In y (remove x m) <-> ~E.eq x y /\ In y m.
Proof.
unfold In; split; [ intros (e,H) | intros (E,(e,H)) ].
- apply remove_mapsto_iff in H. destruct H; split; trivial.
  now exists e.
- exists e. now apply remove_2.
Qed.

Lemma remove_neq_mapsto_iff : forall m x y e,
 ~ E.eq x y -> (MapsTo y e (remove x m)  <-> MapsTo y e m).
Proof.
split; [apply remove_3|apply remove_2]; auto.
Qed.

Lemma remove_neq_in_iff : forall m x y,
 ~ E.eq x y -> (In y (remove x m) <-> In y m).
Proof.
split; intros (e',H0); exists e'.
- now apply remove_3 with x.
- now apply remove_2.
Qed.

Lemma bindings_mapsto_iff m x e :
 MapsTo x e m <-> InA eq_key_elt (x,e) (bindings m).
Proof. symmetry. apply bindings_spec1. Qed.

Lemma bindings_in_iff m x :
 In x m <-> exists e, InA eq_key_elt (x,e) (bindings m).
Proof.
unfold In; split; intros (e,H); exists e; now apply bindings_spec1.
Qed.

End IffSpec.

Lemma map_mapsto_iff {elt elt'} m x b (f : elt -> elt') :
 MapsTo x b (map f m) <-> exists a, b = f a /\ MapsTo x a m.
Proof.
rewrite <-find_spec, map_spec. setoid_rewrite <- find_spec.
destruct (find x m); simpl; split.
- injection 1. now exists e.
- intros (a,(->,H)). now injection H as ->.
- discriminate.
- intros (a,(_,H)); discriminate.
Qed.

Lemma map_in_iff {elt elt'} m x (f : elt -> elt') :
 In x (map f m) <-> In x m.
Proof.
rewrite !in_find, map_spec. apply option_map_some.
Qed.

Lemma mapi_in_iff {elt elt'} m x (f:key->elt->elt') :
 In x (mapi f m) <-> In x m.
Proof.
rewrite !in_find. destruct (mapi_spec f m x) as (y,(_,->)).
apply option_map_some.
Qed.

(** Unfortunately, we don't have simple equivalences for [mapi]
  and [MapsTo]. The only correct one needs compatibility of [f]. *)

Lemma mapi_inv {elt elt'} m x b (f : key -> elt -> elt') :
 MapsTo x b (mapi f m) ->
 exists a y, E.eq y x /\ b = f y a /\ MapsTo x a m.
Proof.
rewrite <- find_spec. setoid_rewrite <- find_spec.
destruct (mapi_spec f m x) as (y,(E,->)).
destruct (find x m); simpl.
- injection 1 as <-. now exists e, y.
- discriminate.
Qed.

Lemma mapi_spec' {elt elt'} (f:key->elt->elt') :
 Proper (E.eq==>Logic.eq==>Logic.eq) f ->
 forall m x,
   find x (mapi f m) = option_map (f x) (find x m).
Proof.
 intros. destruct (mapi_spec f m x) as (y,(Hy,->)).
 destruct (find x m); simpl; trivial.
 now rewrite Hy.
Qed.

Lemma mapi_1bis {elt elt'} m x e (f:key->elt->elt') :
 Proper (E.eq==>Logic.eq==>Logic.eq) f ->
 MapsTo x e m -> MapsTo x (f x e) (mapi f m).
Proof.
intros. destruct (mapi_1 f H0) as (y,(->,H2)). trivial.
Qed.

Lemma mapi_mapsto_iff {elt elt'} m x b (f:key->elt->elt') :
 Proper (E.eq==>Logic.eq==>Logic.eq) f ->
 (MapsTo x b (mapi f m) <-> exists a, b = f x a /\ MapsTo x a m).
Proof.
rewrite <-find_spec. setoid_rewrite <-find_spec.
intros Pr. rewrite mapi_spec' by trivial.
destruct (find x m); simpl; split.
- injection 1 as <-. now exists e.
- intros (a,(->,H)). now injection H as <-.
- discriminate.
- intros (a,(_,H)). discriminate.
Qed.

(** Things are even worse for [merge] : we don't try to state any
 equivalence, see instead boolean results below. *)

(** Useful tactic for simplifying expressions like
   [In y (add x e (remove z m))] *)

Ltac map_iff :=
 repeat (progress (
  rewrite add_mapsto_iff || rewrite add_in_iff ||
  rewrite remove_mapsto_iff || rewrite remove_in_iff ||
  rewrite empty_mapsto_iff || rewrite empty_in_iff ||
  rewrite map_mapsto_iff || rewrite map_in_iff ||
  rewrite mapi_in_iff)).

(** ** Specifications written using boolean predicates *)

Section BoolSpec.

Lemma mem_find_b {elt}(m:t elt)(x:key) :
  mem x m = if find x m then true else false.
Proof.
apply eq_bool_alt. rewrite mem_find. destruct (find x m).
- now split.
- split; (discriminate || now destruct 1).
Qed.

Variable elt elt' elt'' : Type.
Implicit Types m : t elt.
Implicit Types x y z : key.
Implicit Types e : elt.

Lemma mem_b m x y : E.eq x y -> mem x m = mem y m.
Proof. now intros ->. Qed.

Lemma find_o m x y : E.eq x y -> find x m = find y m.
Proof. now intros ->. Qed.

Lemma empty_o x : find x (@empty elt) = None.
Proof. apply empty_spec. Qed.

Lemma empty_a x : mem x (@empty elt) = false.
Proof. apply not_mem_find. apply empty_spec. Qed.

Lemma add_eq_o m x y e :
 E.eq x y -> find y (add x e m) = Some e.
Proof.
 intros <-. apply add_spec1.
Qed.

Lemma add_neq_o m x y e :
 ~ E.eq x y -> find y (add x e m) = find y m.
Proof. apply add_spec2. Qed.
Hint Resolve add_neq_o : map.

Lemma add_o m x y e :
 find y (add x e m) = if E.eq_dec x y then Some e else find y m.
Proof.
destruct (E.eq_dec x y); auto with map.
Qed.

Lemma add_eq_b m x y e :
 E.eq x y -> mem y (add x e m) = true.
Proof.
intros <-. apply mem_spec, add_in_iff. now left.
Qed.

Lemma add_neq_b m x y e :
 ~E.eq x y -> mem y (add x e m) = mem y m.
Proof.
intros. now rewrite !mem_find_b, add_neq_o.
Qed.

Lemma add_b m x y e :
 mem y (add x e m) = eqb x y || mem y m.
Proof.
rewrite !mem_find_b, add_o. unfold eqb.
now destruct (E.eq_dec x y).
Qed.

Lemma remove_eq_o m x y :
 E.eq x y -> find y (remove x m) = None.
Proof. intros ->. apply remove_spec1. Qed.

Lemma remove_neq_o m x y :
 ~ E.eq x y -> find y (remove x m) = find y m.
Proof. apply remove_spec2. Qed.

Hint Resolve remove_eq_o remove_neq_o : map.

Lemma remove_o m x y :
 find y (remove x m) = if E.eq_dec x y then None else find y m.
Proof.
destruct (E.eq_dec x y); auto with map.
Qed.

Lemma remove_eq_b m x y :
 E.eq x y -> mem y (remove x m) = false.
Proof.
intros <-. now rewrite mem_find_b, remove_eq_o.
Qed.

Lemma remove_neq_b m x y :
 ~ E.eq x y -> mem y (remove x m) = mem y m.
Proof.
intros. now rewrite !mem_find_b, remove_neq_o.
Qed.

Lemma remove_b m x y :
 mem y (remove x m) = negb (eqb x y) && mem y m.
Proof.
rewrite !mem_find_b, remove_o; unfold eqb.
now destruct (E.eq_dec x y).
Qed.

Lemma map_o m x (f:elt->elt') :
 find x (map f m) = option_map f (find x m).
Proof. apply map_spec. Qed.

Lemma map_b m x (f:elt->elt') :
 mem x (map f m) = mem x m.
Proof.
rewrite !mem_find_b, map_o. now destruct (find x m).
Qed.

Lemma mapi_b m x (f:key->elt->elt') :
 mem x (mapi f m) = mem x m.
Proof.
apply eq_bool_alt; rewrite !mem_spec. apply mapi_in_iff.
Qed.

Lemma mapi_o m x (f:key->elt->elt') :
 Proper (E.eq==>Logic.eq==>Logic.eq) f ->
 find x (mapi f m) = option_map (f x) (find x m).
Proof. intros; now apply mapi_spec'. Qed.

Lemma merge_spec1' (f:key->option elt->option elt'->option elt'') :
 Proper (E.eq==>Logic.eq==>Logic.eq==>Logic.eq) f ->
 forall (m:t elt)(m':t elt') x,
   In x m \/ In x m' ->
   find x (merge f m m') = f x (find x m) (find x m').
Proof.
 intros Hf m m' x H.
 now destruct (merge_spec1 f H) as (y,(->,->)).
Qed.

Lemma merge_spec1_none (f:key->option elt->option elt'->option elt'') :
 (forall x, f x None None = None) ->
 forall (m: t elt)(m': t elt') x,
 exists y, E.eq y x /\ find x (merge f m m') = f y (find x m) (find x m').
Proof.
intros Hf m m' x.
destruct (find x m) as [e|] eqn:Hm.
- assert (H : In x m \/ In x m') by (left; exists e; now apply find_spec).
  destruct (merge_spec1 f H) as (y,(Hy,->)).
  exists y; split; trivial. now rewrite Hm.
- destruct (find x m') as [e|] eqn:Hm'.
  + assert (H : In x m \/ In x m') by (right; exists e; now apply find_spec).
    destruct (merge_spec1 f H) as (y,(Hy,->)).
    exists y; split; trivial. now rewrite Hm, Hm'.
  + exists x. split. reflexivity. rewrite Hf.
    apply not_in_find. intro H.
    apply merge_spec2 in H. apply not_in_find in Hm. apply not_in_find in Hm'.
    intuition.
Qed.

Lemma merge_spec1'_none (f:key->option elt->option elt'->option elt'') :
 Proper (E.eq==>Logic.eq==>Logic.eq==>Logic.eq) f ->
 (forall x, f x None None = None) ->
 forall (m: t elt)(m': t elt') x,
  find x (merge f m m') = f x (find x m) (find x m').
Proof.
 intros Hf Hf' m m' x.
 now destruct (merge_spec1_none Hf' m m' x) as (y,(->,->)).
Qed.

Lemma bindings_o : forall m x,
 find x m = findA (eqb x) (bindings m).
Proof.
intros. rewrite eq_option_alt. intro e.
rewrite <- find_mapsto_iff, bindings_mapsto_iff.
unfold eqb.
rewrite <- findA_NoDupA; dintuition; try apply bindings_3w; eauto.
Qed.

Lemma bindings_b : forall m x,
 mem x m = existsb (fun p => eqb x (fst p)) (bindings m).
Proof.
intros.
apply eq_bool_alt.
rewrite mem_spec, bindings_in_iff, existsb_exists.
split.
- intros (e,H).
  rewrite InA_alt in H.
  destruct H as ((k,e'),((H1,H2),H')); simpl in *; subst e'.
  exists (k, e); split; trivial. simpl. now apply eqb_eq.
- intros ((k,e),(H,H')); simpl in *. apply eqb_eq in H'.
  exists e. rewrite InA_alt. exists (k,e). now repeat split.
Qed.

End BoolSpec.

Section Equalities.
Variable elt:Type.

(** A few basic equalities *)

Lemma eq_empty (m: t elt) : m == empty <-> is_empty m = true.
Proof.
 unfold Equal. rewrite is_empty_spec. now setoid_rewrite empty_spec.
Qed.

Lemma add_id (m: t elt) x e : add x e m == m <-> find x m = Some e.
Proof.
 split.
 - intros H. rewrite <- (H x). apply add_spec1.
 - intros H y. rewrite !add_o. now destruct E.eq_dec as [<-|E].
Qed.

Lemma add_add_1 (m: t elt) x e :
 add x e (add x e m) == add x e m.
Proof.
 intros y. rewrite !add_o. destruct E.eq_dec; auto.
Qed.

Lemma add_add_2 (m: t elt) x x' e e' :
 ~E.eq x x' -> add x e (add x' e' m) == add x' e' (add x e m).
Proof.
 intros H y. rewrite !add_o.
 do 2 destruct E.eq_dec; auto.
 elim H. now transitivity y.
Qed.

Lemma remove_id (m: t elt) x : remove x m == m <-> ~In x m.
Proof.
 rewrite not_in_find. split.
 - intros H. rewrite <- (H x). apply remove_spec1.
 - intros H y. rewrite !remove_o. now destruct E.eq_dec as [<-|E].
Qed.

Lemma remove_remove_1 (m: t elt) x :
 remove x (remove x m) == remove x m.
Proof.
 intros y. rewrite !remove_o. destruct E.eq_dec; auto.
Qed.

Lemma remove_remove_2 (m: t elt) x x' :
 remove x (remove x' m) == remove x' (remove x m).
Proof.
 intros y. rewrite !remove_o. do 2 destruct E.eq_dec; auto.
Qed.

Lemma remove_add_1 (m: t elt) x e :
  remove x (add x e m) == remove x m.
Proof.
 intro y. rewrite !remove_o, !add_o. now destruct E.eq_dec.
Qed.

Lemma remove_add_2 (m: t elt) x x' e :
  ~E.eq x x' -> remove x' (add x e m) == add x e (remove x' m).
Proof.
 intros H y. rewrite !remove_o, !add_o.
 do 2 destruct E.eq_dec; auto.
 - elim H; now transitivity y.
 - symmetry. now apply remove_eq_o.
 - symmetry. now apply remove_neq_o.
Qed.

Lemma add_remove_1 (m: t elt) x e :
  add x e (remove x m) == add x e m.
Proof.
 intro y. rewrite !add_o, !remove_o. now destruct E.eq_dec.
Qed.

(** Another characterisation of [Equal] *)

Lemma Equal_mapsto_iff : forall m1 m2 : t elt,
 m1 == m2 <-> (forall k e, MapsTo k e m1 <-> MapsTo k e m2).
Proof.
intros m1 m2. split; [intros Heq k e|intros Hiff].
rewrite 2 find_mapsto_iff, Heq. split; auto.
intro k. rewrite eq_option_alt. intro e.
rewrite <- 2 find_mapsto_iff; auto.
Qed.

(** * Relations between [Equal], [Equiv] and [Equivb]. *)

(** First, [Equal] is [Equiv] with Leibniz on elements. *)

Lemma Equal_Equiv : forall (m m' : t elt),
  m == m' <-> Equiv Logic.eq m m'.
Proof.
intros. rewrite Equal_mapsto_iff. split; intros.
- split.
  + split; intros (e,Hin); exists e; [rewrite <- H|rewrite H]; auto.
  + intros; apply mapsto_fun with m k; auto; rewrite H; auto.
- split; intros H'.
  + destruct H.
    assert (Hin : In k m') by (rewrite <- H; exists e; auto).
    destruct Hin as (e',He').
    rewrite (H0 k e e'); auto.
  + destruct H.
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
 forall (m m':t elt), m == m' <-> Equivb cmp m m'.
Proof.
 intros; rewrite Equal_Equiv.
 apply Equiv_Equivb; auto.
Qed.

Lemma Equal_Equivb_eqdec :
 forall eq_elt_dec : (forall e e', { e = e' } + { e <> e' }),
 let cmp := fun e e' => if eq_elt_dec e e' then true else false in
 forall (m m':t elt), m == m' <-> Equivb cmp m m'.
Proof.
intros; apply Equal_Equivb.
unfold cmp; clear cmp; intros.
destruct eq_elt_dec; now intuition.
Qed.

End Equalities.

(** * Results about [fold], [bindings], induction principles... *)

Section Elt.
  Variable elt:Type.

  Definition Add x (e:elt) m m' := m' == (add x e m).

  Notation eqke := (@eq_key_elt elt).
  Notation eqk := (@eq_key elt).

  Instance eqk_equiv : Equivalence eqk.
  Proof. unfold eq_key. destruct E.eq_equiv. constructor; eauto. Qed.

  Instance eqke_equiv : Equivalence eqke.
  Proof.
   unfold eq_key_elt; split; repeat red; intuition; simpl in *;
    etransitivity; eauto.
  Qed.

  (** Complements about InA, NoDupA and findA *)

  Lemma InA_eqke_eqk k k' e e' l :
    E.eq k k' -> InA eqke (k,e) l -> InA eqk (k',e') l.
  Proof.
  intros Hk. rewrite 2 InA_alt.
  intros ((k'',e'') & (Hk'',He'') & H); simpl in *; subst e''.
  exists (k'',e); split; auto. red; simpl. now transitivity k.
  Qed.

  Lemma NoDupA_incl {A} (R R':relation A) :
   (forall x y, R x y -> R' x y) ->
   forall l, NoDupA R' l -> NoDupA R l.
  Proof.
  intros Incl.
  induction 1 as [ | a l E _ IH ]; constructor; auto.
  contradict E. revert E. rewrite 2 InA_alt. firstorder.
  Qed.

  Lemma NoDupA_eqk_eqke l : NoDupA eqk l -> NoDupA eqke l.
  Proof.
  apply NoDupA_incl. now destruct 1.
  Qed.

  Lemma findA_rev l k : NoDupA eqk l ->
    findA (eqb k) l = findA (eqb k) (rev l).
  Proof.
  intros H. apply eq_option_alt. intros e. unfold eqb.
  rewrite <- !findA_NoDupA, InA_rev; eauto with map. reflexivity.
  change (NoDupA eqk (rev l)). apply NoDupA_rev; auto using eqk_equiv.
  Qed.

  (** * Bindings *)

  Lemma bindings_Empty (m:t elt) : Empty m <-> bindings m = nil.
  Proof.
  unfold Empty. split; intros H.
  - assert (H' : forall a, ~ List.In a (bindings m)).
    { intros (k,e) H'. apply (H k e).
      rewrite bindings_mapsto_iff, InA_alt.
      exists (k,e); repeat split; auto with map. }
    destruct (bindings m) as [|p l]; trivial.
    destruct (H' p); simpl; auto.
  - intros x e. rewrite bindings_mapsto_iff, InA_alt.
    rewrite H. now intros (y,(E,H')).
  Qed.

  Lemma bindings_empty : bindings (@empty elt) = nil.
  Proof.
  rewrite <-bindings_Empty; apply empty_1.
  Qed.

  (** * Conversions between maps and association lists. *)

  Definition uncurry {U V W : Type} (f : U -> V -> W) : U*V -> W :=
   fun p => f (fst p) (snd p).

  Definition of_list :=
    List.fold_right (uncurry (@add _)) (@empty elt).

  Definition to_list := bindings.

  Lemma of_list_1 : forall l k e,
    NoDupA eqk l ->
    (MapsTo k e (of_list l) <-> InA eqke (k,e) l).
  Proof.
  induction l as [|(k',e') l IH]; simpl; intros k e Hnodup.
  - rewrite empty_mapsto_iff, InA_nil; intuition.
  - unfold uncurry; simpl.
    inversion_clear Hnodup as [| ? ? Hnotin Hnodup'].
    specialize (IH k e Hnodup'); clear Hnodup'.
    rewrite add_mapsto_iff, InA_cons, <- IH.
    unfold eq_key_elt at 1; simpl.
    split; destruct 1 as [H|H]; try (intuition;fail).
    destruct (E.eq_dec k k'); [left|right]; split; auto with map.
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
  rewrite add_o, IH, eqb_sym. unfold eqb; now destruct E.eq_dec.
  Qed.

  Lemma of_list_2 : forall l, NoDupA eqk l ->
    equivlistA eqke l (to_list (of_list l)).
  Proof.
  intros l Hnodup (k,e).
  rewrite <- bindings_mapsto_iff, of_list_1; intuition.
  Qed.

  Lemma of_list_3 : forall s, Equal (of_list (to_list s)) s.
  Proof.
  intros s k.
  rewrite of_list_1b, bindings_o; auto.
  apply bindings_3w.
  Qed.

  (** * Fold *)

  (** Alternative specification via [fold_right] *)

  Lemma fold_spec_right m (A:Type)(i:A)(f : key -> elt -> A -> A) :
    fold f m i = List.fold_right (uncurry f) i (rev (bindings m)).
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
  set (l:=rev (bindings m)).
  assert (Hstep' : forall k e a m' m'', InA eqke (k,e) l -> ~In k m' ->
             Add k e m' m'' -> P m' a -> P m'' (F (k,e) a)).
  {
   intros k e a m' m'' H ? ? ?; eapply Hstep; eauto.
   revert H; unfold l; rewrite InA_rev, bindings_mapsto_iff; auto with *. }
  assert (Hdup : NoDupA eqk l).
  { unfold l. apply NoDupA_rev; try red; unfold eq_key ; eauto with *.
    apply bindings_3w. }
  assert (Hsame : forall k, find k m = findA (eqb k) l).
  { intros k. unfold l. rewrite bindings_o, findA_rev; auto.
    apply bindings_3w. }
  clearbody l. clearbody F. clear Hstep f. revert m Hsame. induction l.
  - (* empty *)
    intros m Hsame; simpl.
    apply Hempty. intros k e.
    rewrite find_mapsto_iff, Hsame; simpl; discriminate.
  - (* step *)
    intros m Hsame; destruct a as (k,e); simpl.
    apply Hstep' with (of_list l); auto.
    + rewrite InA_cons; left; red; auto with map.
    + inversion_clear Hdup. contradict H. destruct H as (e',He').
      apply InA_eqke_eqk with k e'; auto with map.
      rewrite <- of_list_1; auto.
    + intro k'. rewrite Hsame, add_o, of_list_1b. simpl.
      rewrite eqb_sym. unfold eqb. now destruct E.eq_dec.
      inversion_clear Hdup; auto with map.
    + apply IHl.
      * intros; eapply Hstep'; eauto.
      * inversion_clear Hdup; auto.
      * intros; apply of_list_1b. inversion_clear Hdup; auto.
  Qed.

  (** Same, with [empty] and [add] instead of [Empty] and [Add]. In this
      case, [P] must be compatible with equality of sets *)

  Theorem fold_rec_bis :
    forall (A:Type)(P : t elt -> A -> Type)(f : key -> elt -> A -> A),
     forall (i:A)(m:t elt),
     (forall m m' a, Equal m m' -> P m a -> P m' a) ->
     (P empty i) ->
     (forall k e a m', MapsTo k e m -> ~In k m' ->
       P m' a -> P (add k e m') (f k e a)) ->
     P m (fold f m i).
  Proof.
  intros A P f i m Pmorphism Pempty Pstep.
  apply fold_rec; intros.
  apply Pmorphism with empty; auto. intro k. rewrite empty_o.
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
    P empty i ->
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
  rewrite 2 fold_spec_right. set (l:=rev (bindings m)).
  assert (Rstep' : forall k e a b, InA eqke (k,e) l ->
    R a b -> R (f k e a) (g k e b)).
  { intros; apply Rstep; auto.
    rewrite bindings_mapsto_iff, <- InA_rev; auto with map. }
  clearbody l; clear Rstep m.
  induction l; simpl; auto.
  apply Rstep'; auto.
  destruct a; simpl; rewrite InA_cons; left; red; auto with map.
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
   P empty ->
   (forall x e m, ~In x m -> P m -> P (add x e m)) ->
   forall m, P m.
  Proof.
  intros.
  apply (@fold_rec_bis _ (fun s _ => P s) (fun _ _ _ => tt) tt m); eauto.
  Qed.

  (** [fold] can be used to reconstruct the same initial set. *)

  Lemma fold_identity : forall m : t elt, Equal (fold (@add _) m empty) m.
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

  Variables (A:Type)(eqA:A->A->Prop)(st:Equivalence eqA).

  Lemma fold_Empty (f:key->elt->A->A) :
   forall m i, Empty m -> eqA (fold f m i) i.
  Proof.
  intros. apply fold_rec_nodep with (P:=fun a => eqA a i).
  reflexivity.
  intros. elim (H k e); auto.
  Qed.

  Lemma fold_init (f:key->elt->A->A) :
   Proper (E.eq==>eq==>eqA==>eqA) f ->
   forall m i i', eqA i i' -> eqA (fold f m i) (fold f m i').
  Proof.
  intros Hf m i i' Hi. apply fold_rel with (R:=eqA); auto.
  intros. now apply Hf.
  Qed.

  (** Transpositions of f (a.k.a diamond property).
      Could we swap two sequential calls to f, i.e. do we have:

        f k e (f k' e' a) == f k' e' (f k e a)

      First, we do no need this equation for all keys, but only
      when k and k' aren't equal, as suggested by Pierre Castéran.
      Think for instance of [f] being [M.add] : in general, we don't have
      [M.add k e (M.add k e' m) == M.add k e' (M.add k e m)].
      Fortunately, we will never encounter this situation during a real
      [fold], since the keys received by this [fold] are unique.
      NB: without this condition, this condition would be
      [SetoidList.transpose2].

      Secondly, instead of the equation above, we now use a statement
      with more basic equalities, allowing to prove [fold_commutes] even
      when [f] isn't a morphism.
      NB: When [f] is a morphism, [Diamond f] gives back the equation above.
*)

  Definition Diamond (f:key->elt->A->A) :=
    forall k k' e e' a b b', ~E.eq k k' ->
      eqA (f k e a) b -> eqA (f k' e' a) b' -> eqA (f k e b') (f k' e' b).

  Lemma fold_commutes (f:key->elt->A->A) :
   Diamond f ->
   forall i m k e, ~In k m ->
   eqA (fold f m (f k e i)) (f k e (fold f m i)).
  Proof.
  intros Hf i m k e H.
  apply fold_rel with (R:= fun a b => eqA a (f k e b)); auto.
  - reflexivity.
  - intros k' e' b a Hm E.
    apply Hf with a; try easy.
    contradict H; rewrite <- H. now exists e'.
  Qed.

  Hint Resolve NoDupA_eqk_eqke NoDupA_rev bindings_3w : map.

  Lemma fold_Proper (f:key->elt->A->A) :
   Proper (E.eq==>eq==>eqA==>eqA) f ->
   Diamond f ->
   Proper (Equal==>eqA==>eqA) (fold f).
  Proof.
  intros Hf Hf' m1 m2 Hm i j Hi.
  rewrite 2 fold_spec_right.
  assert (NoDupA eqk (rev (bindings m1))) by (auto with * ).
  assert (NoDupA eqk (rev (bindings m2))) by (auto with * ).
  apply fold_right_equivlistA_restr2 with (R:=complement eqk)(eqA:=eqke)
  ; auto with *.
  - intros (k1,e1) (k2,e2) (Hk,He) a1 a2 Ha; simpl in *. now apply Hf.
  - unfold complement, eq_key, eq_key_elt; repeat red. intuition eauto with map.
  - intros (k,e) (k',e') z z' h h'; unfold eq_key, uncurry;simpl; auto.
    rewrite h'. eapply Hf'; now eauto.
  - rewrite <- NoDupA_altdef; auto.
  - intros (k,e).
    rewrite 2 InA_rev, <- 2 bindings_mapsto_iff, 2 find_mapsto_iff, Hm;
      auto with *.
  Qed.

  Lemma fold_Equal (f:key->elt->A->A) :
   Proper (E.eq==>eq==>eqA==>eqA) f ->
   Diamond f ->
   forall m1 m2 i,
   Equal m1 m2 ->
   eqA (fold f m1 i) (fold f m2 i).
  Proof.
   intros. now apply fold_Proper.
  Qed.

  Lemma fold_Add (f:key->elt->A->A) :
   Proper (E.eq==>eq==>eqA==>eqA) f ->
   Diamond f ->
   forall m1 m2 k e i, ~In k m1 -> Add k e m1 m2 ->
   eqA (fold f m2 i) (f k e (fold f m1 i)).
  Proof.
  intros Hf Hf' m1 m2 k e i Hm1 Hm2.
  rewrite 2 fold_spec_right.
  set (f':=uncurry f).
  change (f k e (fold_right f' i (rev (bindings m1))))
   with (f' (k,e) (fold_right f' i (rev (bindings m1)))).
  assert (NoDupA eqk (rev (bindings m1))) by (auto with * ).
  assert (NoDupA eqk (rev (bindings m2))) by (auto with * ).
  apply fold_right_add_restr with
   (R:=complement eqk)(eqA:=eqke); auto with *.
  - intros (k1,e1) (k2,e2) (Hk,He) a a' Ha; unfold f'; simpl in *. now apply Hf.
  - unfold complement, eq_key_elt, eq_key; repeat red; intuition eauto with map.
  - intros (k1,e1) (k2,e2) z1 z2; unfold eq_key, f', uncurry; simpl.
    eapply Hf'; now eauto.
  - rewrite <- NoDupA_altdef; auto.
  - rewrite InA_rev, <- bindings_mapsto_iff by (auto with * ). firstorder.
  - intros (a,b).
    rewrite InA_cons, 2 InA_rev, <- 2 bindings_mapsto_iff,
    2 find_mapsto_iff by (auto with * ).
    unfold eq_key_elt; simpl.
    rewrite Hm2, !find_spec, add_mapsto_new; intuition.
  Qed.

  Lemma fold_add (f:key->elt->A->A) :
   Proper (E.eq==>eq==>eqA==>eqA) f ->
   Diamond f ->
   forall m k e i, ~In k m ->
   eqA (fold f (add k e m) i) (f k e (fold f m i)).
  Proof.
  intros. now apply fold_Add.
  Qed.

  End Fold_More.

  (** * Cardinal *)

  Lemma cardinal_fold (m : t elt) :
   cardinal m = fold (fun _ _ => S) m 0.
  Proof.
  rewrite cardinal_1, fold_1.
  symmetry; apply fold_left_length; auto.
  Qed.

  Lemma cardinal_Empty : forall m : t elt,
   Empty m <-> cardinal m = 0.
  Proof.
  intros.
  rewrite cardinal_1, bindings_Empty.
  destruct (bindings m); intuition; discriminate.
  Qed.

  Lemma Equal_cardinal (m m' : t elt) :
    Equal m m' -> cardinal m = cardinal m'.
  Proof.
  intro. rewrite 2 cardinal_fold.
  apply fold_Equal with (eqA:=eq); try congruence; auto with map.
  Qed.

  Lemma cardinal_0 (m : t elt) : Empty m -> cardinal m = 0.
  Proof.
  intros; rewrite <- cardinal_Empty; auto.
  Qed.

  Lemma cardinal_S m m' x e :
    ~ In x m -> Add x e m m' -> cardinal m' = S (cardinal m).
  Proof.
  intros. rewrite 2 cardinal_fold.
  change S with ((fun _ _ => S) x e).
  apply fold_Add with (eqA:=eq); try congruence; auto with map.
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
  intros; rewrite M.cardinal_spec in *.
  generalize (bindings_mapsto_iff m).
  destruct (bindings m); try discriminate.
  exists p; auto.
  rewrite H0; destruct p; simpl; auto.
  constructor; red; auto with map.
  Qed.

  Lemma cardinal_inv_2b :
   forall m, cardinal m <> 0 -> { p : key*elt | MapsTo (fst p) (snd p) m }.
  Proof.
  intros.
  generalize (@cardinal_inv_2 m); destruct cardinal.
  elim H;auto.
  eauto.
  Qed.

  Lemma not_empty_mapsto (m : t elt) :
    ~Empty m -> exists k e, MapsTo k e m.
  Proof.
  intro.
  destruct (@cardinal_inv_2b m) as ((k,e),H').
  contradict H. now apply cardinal_inv_1.
  exists k; now exists e.
  Qed.

  Lemma not_empty_in (m:t elt) :
    ~Empty m -> exists k, In k m.
  Proof.
  intro. destruct (not_empty_mapsto H) as (k,Hk).
  now exists k.
  Qed.

  (** * Additional notions over maps *)

  Definition Disjoint (m m' : t elt) :=
   forall k, ~(In k m /\ In k m').

  Definition Partition (m m1 m2 : t elt) :=
    Disjoint m1 m2 /\
    (forall k e, MapsTo k e m <-> MapsTo k e m1 \/ MapsTo k e m2).

  (** * Emulation of some functions lacking in the interface *)

  Definition filter (f : key -> elt -> bool)(m : t elt) :=
   fold (fun k e m => if f k e then add k e m else m) m empty.

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

  (** Properties of these abbreviations *)

  Lemma filter_iff (f : key -> elt -> bool) :
    Proper (E.eq==>eq==>eq) f ->
    forall m k e,
      MapsTo k e (filter f m) <-> MapsTo k e m /\ f k e = true.
  Proof.
  unfold filter.
  set (f':=fun k e m => if f k e then add k e m else m).
  intros Hf m. pattern m, (fold f' m empty). apply fold_rec.

  - intros m' Hm' k e. rewrite empty_mapsto_iff. intuition.
    elim (Hm' k e); auto.

  - intros k e acc m1 m2 Hke Hn Hadd IH k' e'.
    change (Equal m2 (add k e m1)) in Hadd; rewrite Hadd.
    unfold f'; simpl.
    rewrite add_mapsto_new by trivial.
    case_eq (f k e); intros Hfke; simpl;
     rewrite ?add_mapsto_iff, IH; clear IH; intuition.
    + rewrite <- Hfke; apply Hf; auto with map.
    + right. repeat split; trivial. contradict Hn. rewrite Hn. now exists e'.
    + assert (f k e = f k' e') by (apply Hf; auto). congruence.
  Qed.

  Lemma for_all_filter f m :
   for_all f m = is_empty (filter (fun k e => negb (f k e)) m).
  Proof.
   unfold for_all, filter.
   eapply fold_rel with (R:=fun x y => x = is_empty y).
   - symmetry. apply is_empty_iff. apply empty_1.
   - intros; subst. destruct (f k e); simpl; trivial.
     symmetry. apply not_true_is_false. rewrite is_empty_spec.
     intros H'. specialize (H' k). now rewrite add_spec1 in H'.
  Qed.

  Lemma exists_filter f m :
   exists_ f m = negb (is_empty (filter f m)).
  Proof.
   unfold for_all, filter.
   eapply fold_rel with (R:=fun x y => x = negb (is_empty y)).
   - symmetry. rewrite negb_false_iff. apply is_empty_iff. apply empty_1.
   - intros; subst. destruct (f k e); simpl; trivial.
     symmetry. rewrite negb_true_iff. apply not_true_is_false.
     rewrite is_empty_spec.
     intros H'. specialize (H' k). now rewrite add_spec1 in H'.
  Qed.

  Lemma for_all_iff f m :
   Proper (E.eq==>eq==>eq) f ->
   (for_all f m = true <-> (forall k e, MapsTo k e m -> f k e = true)).
  Proof.
  intros Hf.
  rewrite for_all_filter.
  rewrite <- is_empty_iff. unfold Empty.
  split; intros H k e; specialize (H k e);
   rewrite filter_iff in * by solve_proper; intuition.
  - destruct (f k e); auto.
  - now rewrite H0 in H2.
  Qed.

  Lemma exists_iff f m :
   Proper (E.eq==>eq==>eq) f ->
   (exists_ f m = true <->
     (exists k e, MapsTo k e m /\ f k e = true)).
  Proof.
  intros Hf.
  rewrite exists_filter. rewrite negb_true_iff.
  rewrite <- not_true_iff_false, <- is_empty_iff.
  split.
  - intros H. apply not_empty_mapsto in H. now setoid_rewrite filter_iff in H.
  - unfold Empty. setoid_rewrite filter_iff; trivial. firstorder.
  Qed.

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
  intros (U,V) (W,Z). rewrite <- (mapsto_fun U W) in Z; congruence.
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
  { change (Equal m' (add x e m)) in Hadd. rewrite Hadd.
    intro k. rewrite remove_o, add_o.
    destruct E.eq_dec as [He|Hne]; auto.
    rewrite <- He, <- not_find_in_iff; auto. }
  assert (H : MapsTo x e m').
  { change (Equal m' (add x e m)) in Hadd; rewrite Hadd.
    apply add_1; auto with map. }
  rewrite Hor in H; destruct H.

  - (* first case : x in m1 *)
    exists (remove x m1); left. split; [|split].
    + (* add *)
      change (Equal m1 (add x e (remove x m1))).
      intro k.
      rewrite add_o, remove_o.
      destruct E.eq_dec as [He|Hne]; auto.
      rewrite <- He; apply find_1; auto.
    + (* disjoint *)
      intros k (H1,H2). elim (Hdisj k). split; auto.
      rewrite remove_in_iff in H1; destruct H1; auto.
    + (* mapsto *)
      intros k' e'.
      rewrite Heq, 2 remove_mapsto_iff, Hor.
      intuition.
      elim (Hdisj x); split; [exists e|exists e']; auto.
      apply MapsTo_1 with k'; auto with map.

  - (* second case : x in m2 *)
    exists (remove x m2); right. split; [|split].
    + (* add *)
      change (Equal m2 (add x e (remove x m2))).
      intro k.
      rewrite add_o, remove_o.
      destruct E.eq_dec as [He|Hne]; auto.
      rewrite <- He; apply find_1; auto.
    + (* disjoint *)
      intros k (H1,H2). elim (Hdisj k). split; auto.
      rewrite remove_in_iff in H2; destruct H2; auto.
    + (* mapsto *)
      intros k' e'.
      rewrite Heq, 2 remove_mapsto_iff, Hor.
      intuition.
      elim (Hdisj x); split; [exists e'|exists e]; auto.
      apply MapsTo_1 with k'; auto with map.
  Qed.

  Lemma Partition_fold :
   forall (A:Type)(eqA:A->A->Prop)(st:Equivalence eqA)(f:key->elt->A->A),
   Proper (E.eq==>eq==>eqA==>eqA) f ->
   Diamond eqA f ->
   forall m m1 m2 i,
   Partition m m1 m2 ->
   eqA (fold f m i) (fold f m1 (fold f m2 i)).
  Proof.
  intros A eqA st f Comp Tra.
  induction m as [m Hm|m m' IH k e Hn Hadd] using map_induction.

  - intros m1 m2 i Hp. rewrite (fold_Empty (eqA:=eqA)); auto.
    rewrite (Partition_Empty Hp) in Hm. destruct Hm.
    rewrite 2 (fold_Empty (eqA:=eqA)); auto. reflexivity.

  - intros m1 m2 i Hp.
    destruct (Partition_Add Hn Hadd Hp) as (m3,[(Hadd',Hp')|(Hadd',Hp')]).
    + (* fst case: m3 is (k,e)::m1 *)
      assert (~In k m3).
      { contradict Hn. destruct Hn as (e',He').
        destruct Hp' as (Hp1,Hp2). exists e'. rewrite Hp2; auto. }
      transitivity (f k e (fold f m i)).
      apply fold_Add with (eqA:=eqA); auto.
      symmetry.
      transitivity (f k e (fold f m3 (fold f m2 i))).
      apply fold_Add with (eqA:=eqA); auto.
      apply Comp; auto with map.
      symmetry; apply IH; auto.
    + (* snd case: m3 is (k,e)::m2 *)
      assert (~In k m3).
      { contradict Hn. destruct Hn as (e',He').
        destruct Hp' as (Hp1,Hp2). exists e'. rewrite Hp2; auto. }
      assert (~In k m1).
      { contradict Hn. destruct Hn as (e',He').
        destruct Hp' as (Hp1,Hp2). exists e'. rewrite Hp2; auto. }
      transitivity (f k e (fold f m i)).
      apply fold_Add with (eqA:=eqA); auto.
      transitivity (f k e (fold f m1 (fold f m3 i))).
      apply Comp; auto using IH with map.
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
  apply Partition_fold with (eqA:=eq); compute; auto with map. congruence.
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

  - intros m0 Hm0 k e.
    assert (~In k m0) by (intros (e0,He0); apply (Hm0 k e0); auto).
    intuition.
    elim (Hm0 k e); auto.

  - intros k e m0 m1 m2 _ Hn Hadd IH k' e'.
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

  (** specialized versions analyzing only keys (resp. bindings) *)

  Definition filter_dom (f : key -> bool) := filter (fun k _ => f k).
  Definition filter_range (f : elt -> bool) := filter (fun _ => f).
  Definition for_all_dom (f : key -> bool) := for_all (fun k _ => f k).
  Definition for_all_range (f : elt -> bool) := for_all (fun _ => f).
  Definition exists_dom (f : key -> bool) := exists_ (fun k _ => f k).
  Definition exists_range (f : elt -> bool) := exists_ (fun _ => f).
  Definition partition_dom (f : key -> bool) := partition (fun k _ => f k).
  Definition partition_range (f : elt -> bool) := partition (fun _ => f).

 End Elt.

 Instance cardinal_m {elt} : Proper (Equal ==> Logic.eq) (@cardinal elt).
 Proof. intros m m'. apply Equal_cardinal. Qed.

 Instance Disjoint_m {elt} : Proper (Equal ==> Equal ==> iff) (@Disjoint elt).
 Proof.
  intros m1 m1' Hm1 m2 m2' Hm2. unfold Disjoint. split; intros.
  rewrite <- Hm1, <- Hm2; auto.
  rewrite Hm1, Hm2; auto.
 Qed.

 Instance Partition_m {elt} :
   Proper (Equal ==> Equal ==> Equal ==> iff) (@Partition elt).
 Proof.
  intros m1 m1' Hm1 m2 m2' Hm2 m3 m3' Hm3. unfold Partition.
  rewrite <- Hm2, <- Hm3.
  split; intros (H,H'); split; auto; intros.
  rewrite <- Hm1, <- Hm2, <- Hm3; auto.
  rewrite Hm1, Hm2, Hm3; auto.
 Qed.

(*
 Instance filter_m0 {elt} (f:key->elt->bool) :
   Proper (E.eq==>Logic.eq==>Logic.eq) f ->
   Proper (Equal==>Equal) (filter f).
 Proof.
  intros Hf m m' Hm. apply Equal_mapsto_iff. intros.
  now rewrite !filter_iff, Hm.
 Qed.
*)

 Instance filter_m {elt} :
   Proper ((E.eq==>Logic.eq==>Logic.eq)==>Equal==>Equal) (@filter elt).
 Proof.
  intros f f' Hf m m' Hm. unfold filter.
  rewrite 2 fold_spec_right.
  set (l := rev (bindings m)).
  set (l' := rev (bindings m')).
  set (op := fun (f:key->elt->bool) =>
             uncurry (fun k e acc => if f k e then add k e acc else acc)).
  change (Equal (fold_right (op f) empty l) (fold_right (op f') empty l')).
  assert (Hl : NoDupA eq_key l).
  { apply NoDupA_rev. apply eqk_equiv. apply bindings_spec2w. }
  assert (Hl' : NoDupA eq_key l').
  { apply NoDupA_rev. apply eqk_equiv. apply bindings_spec2w. }
  assert (H : PermutationA eq_key_elt l l').
  { apply NoDupA_equivlistA_PermutationA.
    - apply eqke_equiv.
    - now apply NoDupA_eqk_eqke.
    - now apply NoDupA_eqk_eqke.
    - intros (k,e); unfold l, l'. rewrite 2 InA_rev, 2 bindings_spec1.
      rewrite Equal_mapsto_iff in Hm. apply Hm. }
  destruct (PermutationA_decompose (eqke_equiv _) H) as (l0,(P,E)).
  transitivity (fold_right (op f) empty l0).
  - apply fold_right_equivlistA_restr2
     with (eqA:=Logic.eq)(R:=complement eq_key); auto with *.
    + intros p p' <- acc acc' Hacc.
      destruct p as (k,e); unfold op, uncurry; simpl.
      destruct (f k e); now rewrite Hacc.
    + intros (k,e) (k',e') z z'.
      unfold op, complement, uncurry, eq_key; simpl.
      intros Hk Hz.
      destruct (f k e), (f k' e'); rewrite <- Hz; try reflexivity.
      now apply add_add_2.
    + apply NoDupA_incl with eq_key; trivial. intros; subst; now red.
    + apply PermutationA_preserves_NoDupA with l; auto with *.
      apply Permutation_PermutationA; auto with *.
      apply NoDupA_incl with eq_key; trivial. intros; subst; now red.
    + apply NoDupA_altdef. apply NoDupA_rev. apply eqk_equiv.
      apply bindings_spec2w.
    + apply PermutationA_equivlistA; auto with *.
      apply Permutation_PermutationA; auto with *.
  - clearbody l'. clear l Hl Hl' H P m m' Hm.
    induction E.
    + reflexivity.
    + simpl. destruct x as (k,e), x' as (k',e').
      unfold op, uncurry at 1 3; simpl.
      destruct H; simpl in *. rewrite <- (Hf _ _ H _ _ H0).
      destruct (f k e); trivial. now f_equiv.
 Qed.

 Instance for_all_m {elt} :
   Proper ((E.eq==>Logic.eq==>Logic.eq)==>Equal==>Logic.eq) (@for_all elt).
 Proof.
 intros f f' Hf m m' Hm. rewrite 2 for_all_filter.
 (* Strange: we cannot rewrite Hm here... *)
 f_equiv. f_equiv; trivial.
 intros k k' Hk e e' He. f_equal. now apply Hf.
 Qed.

 Instance exists_m {elt} :
   Proper ((E.eq==>Logic.eq==>Logic.eq)==>Equal==>Logic.eq) (@exists_ elt).
 Proof.
 intros f f' Hf m m' Hm. rewrite 2 exists_filter.
 f_equal. now apply is_empty_m, filter_m.
 Qed.

 Fact diamond_add {elt} : Diamond Equal (@add elt).
 Proof.
  intros k k' e e' a b b' Hk <- <-. now apply add_add_2.
 Qed.

 Instance update_m {elt} : Proper (Equal ==> Equal ==> Equal) (@update elt).
 Proof.
  intros m1 m1' Hm1 m2 m2' Hm2.
  unfold update.
  apply fold_Proper; auto using diamond_add with *.
 Qed.

 Instance restrict_m {elt} : Proper (Equal==>Equal==>Equal) (@restrict elt).
 Proof.
  intros m1 m1' Hm1 m2 m2' Hm2 y.
  unfold restrict.
  apply eq_option_alt. intros e.
  rewrite !find_spec, !filter_iff, Hm1, Hm2. reflexivity.
  clear. intros x x' Hx e e' He. now rewrite Hx.
  clear. intros x x' Hx e e' He. now rewrite Hx.
 Qed.

 Instance diff_m {elt} : Proper (Equal==>Equal==>Equal) (@diff elt).
 Proof.
  intros m1 m1' Hm1 m2 m2' Hm2 y.
  unfold diff.
  apply eq_option_alt. intros e.
  rewrite !find_spec, !filter_iff, Hm1, Hm2. reflexivity.
  clear. intros x x' Hx e e' He. now rewrite Hx.
  clear. intros x x' Hx e e' He. now rewrite Hx.
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
 Import M.

 Section Elt.
  Variable elt:Type.

  Definition Above x (m:t elt) := forall y, In y m -> E.lt y x.
  Definition Below x (m:t elt) := forall y, In y m -> E.lt x y.

  Section Bindings.

  Lemma sort_equivlistA_eqlistA : forall l l' : list (key*elt),
   sort ltk l -> sort ltk l' -> equivlistA eqke l l' -> eqlistA eqke l l'.
  Proof.
  apply SortA_equivlistA_eqlistA; eauto with *.
  Qed.

  Ltac klean := unfold O.eqke, O.ltk, RelCompFun in *; simpl in *.
  Ltac keauto := klean; intuition; eauto.

  Definition gtb (p p':key*elt) :=
    match E.compare (fst p) (fst p') with Gt => true | _ => false end.
  Definition leb p := fun p' => negb (gtb p p').

  Definition bindings_lt p m := List.filter (gtb p) (bindings m).
  Definition bindings_ge p m := List.filter (leb p) (bindings m).

  Lemma gtb_1 : forall p p', gtb p p' = true <-> ltk p' p.
  Proof.
   intros (x,e) (y,e'); unfold gtb; klean.
   case E.compare_spec; intuition; try discriminate; ME.order.
  Qed.

  Lemma leb_1 : forall p p', leb p p' = true <-> ~ltk p' p.
  Proof.
   intros (x,e) (y,e'); unfold leb, gtb; klean.
   case E.compare_spec; intuition; try discriminate; ME.order.
  Qed.

  Instance gtb_compat : forall p, Proper (eqke==>eq) (gtb p).
  Proof.
   red; intros (x,e) (a,e') (b,e'') H; red in H; simpl in *; destruct H.
   generalize (gtb_1 (x,e) (a,e'))(gtb_1 (x,e) (b,e''));
    destruct (gtb (x,e) (a,e')); destruct (gtb (x,e) (b,e'')); klean; auto.
   - intros. symmetry; rewrite H2. rewrite <-H, <-H1; auto.
   - intros. rewrite H1. rewrite H, <- H2; auto.
  Qed.

  Instance leb_compat : forall p, Proper (eqke==>eq) (leb p).
  Proof.
   intros x a b H. unfold leb; f_equal; apply gtb_compat; auto.
  Qed.

  Hint Resolve gtb_compat leb_compat bindings_spec2 : map.

  Lemma bindings_split : forall p m,
    bindings m = bindings_lt p m ++ bindings_ge p m.
  Proof.
  unfold bindings_lt, bindings_ge, leb; intros.
  apply filter_split with (eqA:=eqk) (ltA:=ltk); eauto with *.
  intros; destruct x; destruct y; destruct p.
  rewrite gtb_1 in H; klean.
  apply not_true_iff_false in H0. rewrite gtb_1 in H0. klean. ME.order.
  Qed.

  Lemma bindings_Add : forall m m' x e, ~In x m -> Add x e m m' ->
    eqlistA eqke (bindings m')
                 (bindings_lt (x,e) m ++ (x,e):: bindings_ge (x,e) m).
  Proof.
  intros; unfold bindings_lt, bindings_ge.
  apply sort_equivlistA_eqlistA; auto with *.
  - apply (@SortA_app _ eqke); auto with *.
    + apply (@filter_sort _ eqke); auto with *; keauto.
    + constructor; auto with map.
      * apply (@filter_sort _ eqke); auto with *; keauto.
      * rewrite (@InfA_alt _ eqke); auto with *; try (keauto; fail).
        { intros.
          rewrite filter_InA in H1; auto with *; destruct H1.
          rewrite leb_1 in H2.
          destruct y; klean.
          rewrite <- bindings_mapsto_iff in H1.
          assert (~E.eq x t0).
          { contradict H.
            exists e0; apply MapsTo_1 with t0; auto.
            ME.order. }
          ME.order. }
        { apply (@filter_sort _ eqke); auto with *; keauto. }
    + intros.
      rewrite filter_InA in H1; auto with *; destruct H1.
      rewrite gtb_1 in H3.
      destruct y; destruct x0; klean.
      inversion_clear H2.
      * red in H4; klean; destruct H4; simpl in *. ME.order.
      * rewrite filter_InA in H4; auto with *; destruct H4.
        rewrite leb_1 in H4. klean; ME.order.
  - intros (k,e').
    rewrite InA_app_iff, InA_cons, 2 filter_InA,
      <-2 bindings_mapsto_iff, leb_1, gtb_1,
      find_mapsto_iff, (H0 k), <- find_mapsto_iff,
      add_mapsto_iff by (auto with * ).
    change (eqke (k,e') (x,e)) with (E.eq k x /\ e' = e).
    klean.
    split.
    + intros [(->,->)|(Hk,Hm)].
      * right; now left.
      * destruct (lt_dec k x); intuition.
    + intros [(Hm,LT)|[(->,->)|(Hm,EQ)]].
      * right; split; trivial; ME.order.
      * now left.
      * destruct (eq_dec x k) as [Hk|Hk].
        elim H. exists e'. now rewrite Hk.
        right; auto.
  Qed.

  Lemma bindings_Add_Above : forall m m' x e,
   Above x m -> Add x e m m' ->
     eqlistA eqke (bindings m') (bindings m ++ (x,e)::nil).
  Proof.
  intros.
  apply sort_equivlistA_eqlistA; auto with *.
  apply (@SortA_app _ eqke); auto with *.
  intros.
  inversion_clear H2.
  destruct x0; destruct y.
  rewrite <- bindings_mapsto_iff in H1.
  destruct H3; klean.
  rewrite H2.
  apply H; firstorder.
  inversion H3.
  red; intros a; destruct a.
  rewrite InA_app_iff, InA_cons, InA_nil, <- 2 bindings_mapsto_iff,
   find_mapsto_iff, (H0 t0), <- find_mapsto_iff,
   add_mapsto_iff by (auto with *).
  change (eqke (t0,e0) (x,e)) with (E.eq t0 x /\ e0 = e).
  intuition.
  destruct (E.eq_dec x t0) as [Heq|Hneq]; auto.
  exfalso.
  assert (In t0 m) by (exists e0; auto).
  generalize (H t0 H1).
  ME.order.
  Qed.

  Lemma bindings_Add_Below : forall m m' x e,
   Below x m -> Add x e m m' ->
     eqlistA eqke (bindings m') ((x,e)::bindings m).
  Proof.
  intros.
  apply sort_equivlistA_eqlistA; auto with *.
  change (sort ltk (((x,e)::nil) ++ bindings m)).
  apply (@SortA_app _ eqke); auto with *.
  intros.
  inversion_clear H1.
  destruct y; destruct x0.
  rewrite <- bindings_mapsto_iff in H2.
  destruct H3; klean.
  rewrite H1.
  apply H; firstorder.
  inversion H3.
  red; intros a; destruct a.
  rewrite InA_cons, <- 2 bindings_mapsto_iff,
    find_mapsto_iff, (H0 t0), <- find_mapsto_iff,
    add_mapsto_iff by (auto with * ).
  change (eqke (t0,e0) (x,e)) with (E.eq t0 x /\ e0 = e).
  intuition.
  destruct (E.eq_dec x t0) as [Heq|Hneq]; auto.
  exfalso.
  assert (In t0 m) by (exists e0; auto).
  generalize (H t0 H1).
  ME.order.
  Qed.

  Lemma bindings_Equal_eqlistA : forall (m m': t elt),
   Equal m m' -> eqlistA eqke (bindings m) (bindings m').
  Proof.
  intros.
  apply sort_equivlistA_eqlistA; auto with *.
  red; intros.
  destruct x; do 2 rewrite <- bindings_mapsto_iff.
  do 2 rewrite find_mapsto_iff; rewrite H; split; auto.
  Qed.

  End Bindings.

  Section Min_Max_Elt.

  (** We emulate two [max_elt] and [min_elt] functions. *)

  Fixpoint max_elt_aux (l:list (key*elt)) := match l with
    | nil => None
    | (x,e)::nil => Some (x,e)
    | (x,e)::l => max_elt_aux l
    end.
  Definition max_elt m := max_elt_aux (bindings m).

  Lemma max_elt_Above :
   forall m x e, max_elt m = Some (x,e) -> Above x (remove x m).
  Proof.
  red; intros.
  rewrite remove_in_iff in H0.
  destruct H0.
  rewrite bindings_in_iff in H1.
  destruct H1.
  unfold max_elt in *.
  generalize (bindings_spec2 m).
  revert x e H y x0 H0 H1.
  induction (bindings m).
  simpl; intros; try discriminate.
  intros.
  destruct a; destruct l; simpl in *.
  injection H; clear H; intros; subst.
  inversion_clear H1.
  red in H; simpl in *; intuition.
  now elim H0.
  inversion H.
  change (max_elt_aux (p::l) = Some (x,e)) in H.
  generalize (IHl x e H); clear IHl; intros IHl.
  inversion_clear H1; [ | inversion_clear H2; eauto ].
  red in H3; simpl in H3; destruct H3.
  destruct p as (p1,p2).
  destruct (E.eq_dec p1 x) as [Heq|Hneq].
  rewrite <- Heq; auto.
   inversion_clear H2.
   inversion_clear H5.
   red in H2; simpl in H2; ME.order.
  transitivity p1; auto.
   inversion_clear H2.
   inversion_clear H5.
   red in H2; simpl in H2; ME.order.
  eapply IHl; eauto with *.
  econstructor; eauto.
  red; eauto with *.
  inversion H2; auto.
  Qed.

  Lemma max_elt_MapsTo :
   forall m x e, max_elt m = Some (x,e) -> MapsTo x e m.
  Proof.
  intros.
  unfold max_elt in *.
  rewrite bindings_mapsto_iff.
  induction (bindings m).
  simpl; try discriminate.
  destruct a; destruct l; simpl in *.
  injection H; intros; subst; constructor; red; auto with *.
  constructor 2; auto.
  Qed.

  Lemma max_elt_Empty :
   forall m, max_elt m = None -> Empty m.
  Proof.
  intros.
  unfold max_elt in *.
  rewrite bindings_Empty.
  induction (bindings m); auto.
  destruct a; destruct l; simpl in *; try discriminate.
  assert (H':=IHl H); discriminate.
  Qed.

  Definition min_elt m : option (key*elt) := match bindings m with
   | nil => None
   | (x,e)::_ => Some (x,e)
  end.

  Lemma min_elt_Below :
   forall m x e, min_elt m = Some (x,e) -> Below x (remove x m).
  Proof.
  unfold min_elt, Below; intros.
  rewrite remove_in_iff in H0; destruct H0.
  rewrite bindings_in_iff in H1.
  destruct H1.
  generalize (bindings_spec2 m).
  destruct (bindings m).
  try discriminate.
  destruct p; injection H; intros; subst.
  inversion_clear H1.
  red in H2; destruct H2; simpl in *; ME.order.
  inversion_clear H4.
  rewrite (@InfA_alt _ eqke) in H3; eauto with *.
  apply (H3 (y,x0)); auto.
  Qed.

  Lemma min_elt_MapsTo :
   forall m x e, min_elt m = Some (x,e) -> MapsTo x e m.
  Proof.
  intros.
  unfold min_elt in *.
  rewrite bindings_mapsto_iff.
  destruct (bindings m).
  simpl; try discriminate.
  destruct p; simpl in *.
  injection H; intros; subst; constructor; red; auto with *.
  Qed.

  Lemma min_elt_Empty :
   forall m, min_elt m = None -> Empty m.
  Proof.
  intros.
  unfold min_elt in *.
  rewrite bindings_Empty.
  destruct (bindings m); auto.
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
  { apply max_elt_MapsTo, find_spec, add_id in H.
    unfold Add. symmetry. now rewrite add_remove_1. }
  apply X0 with (remove k m) k e; auto with map.
  apply IHn.
  assert (S n = S (cardinal (remove k m))).
  { rewrite Heqn.
    eapply cardinal_S; eauto with map. }
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
  { apply min_elt_MapsTo, find_spec, add_id in H.
    unfold Add. symmetry. now rewrite add_remove_1. }
  apply X0 with (remove k m) k e; auto.
  apply IHn.
  assert (S n = S (cardinal (remove k m))).
  { rewrite Heqn.
    eapply cardinal_S; eauto with map. }
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
  apply eqlistA_rev. apply bindings_Equal_eqlistA. auto.
  Qed.

  Lemma fold_Add_Above : forall m1 m2 x e (A:Type)(eqA:A->A->Prop)(st:Equivalence eqA)
   (f:key->elt->A->A)(i:A) (P:Proper (E.eq==>eq==>eqA==>eqA) f),
   Above x m1 -> Add x e m1 m2 ->
   eqA (fold f m2 i) (f x e (fold f m1 i)).
  Proof.
  intros. rewrite 2 fold_spec_right. set (f':=uncurry f).
  transitivity (fold_right f' i (rev (bindings m1 ++ (x,e)::nil))).
  apply fold_right_eqlistA with (eqA:=eqke) (eqB:=eqA); auto.
  intros (k1,e1) (k2,e2) (Hk,He) a1 a2 Ha; unfold f'; simpl in *. apply P; auto.
  apply eqlistA_rev.
  apply bindings_Add_Above; auto.
  rewrite distr_rev; simpl.
  reflexivity.
  Qed.

  Lemma fold_Add_Below : forall m1 m2 x e (A:Type)(eqA:A->A->Prop)(st:Equivalence eqA)
   (f:key->elt->A->A)(i:A) (P:Proper (E.eq==>eq==>eqA==>eqA) f),
   Below x m1 -> Add x e m1 m2 ->
   eqA (fold f m2 i) (fold f m1 (f x e i)).
  Proof.
  intros. rewrite 2 fold_spec_right. set (f':=uncurry f).
  transitivity (fold_right f' i (rev (((x,e)::nil)++bindings m1))).
  apply fold_right_eqlistA with (eqA:=eqke) (eqB:=eqA); auto.
  intros (k1,e1) (k2,e2) (Hk,He) a1 a2 Ha; unfold f'; simpl in *; apply P; auto.
  apply eqlistA_rev.
  simpl; apply bindings_Add_Below; auto.
  rewrite distr_rev; simpl.
  rewrite fold_right_app.
  reflexivity.
  Qed.

  End Fold_properties.

 End Elt.

End OrdProperties.
