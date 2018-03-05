(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export List.
Require Export BinPos.
Require Arith.EqNat.

Open Scope positive_scope.

Ltac clean := try (simpl; congruence).

Lemma Gt_Psucc: forall p q,
       (p ?= Pos.succ q) = Gt -> (p ?= q) = Gt.
Proof.
intros. rewrite <- Pos.compare_succ_succ.
now apply Pos.lt_gt, Pos.lt_lt_succ, Pos.gt_lt.
Qed.

Lemma Psucc_Gt : forall p,
       (Pos.succ p ?= p) = Gt.
Proof.
intros. apply Pos.lt_gt, Pos.lt_succ_diag_r.
Qed.

Fixpoint Lget (A:Set) (n:nat) (l:list A) {struct l}:option A :=
match l with nil => None
| x::q =>
match n with O => Some x
| S m => Lget A m q
end end .

Arguments Lget [A] n l.

Lemma map_app : forall (A B:Set) (f:A -> B) l m,
List.map  f (l ++ m) = List.map  f  l ++ List.map  f  m.
induction l.
reflexivity.
simpl.
intro m ; apply f_equal;apply IHl.
Qed.

Lemma length_map : forall (A B:Set) (f:A -> B) l,
length (List.map  f l) = length l.
induction l.
reflexivity.
simpl; apply f_equal;apply IHl.
Qed.

Lemma Lget_map : forall (A B:Set) (f:A -> B) i l,
Lget i (List.map  f l) =
match Lget i l with Some a =>
Some (f a) | None => None end.
induction i;intros [ | x l ] ;trivial.
simpl;auto.
Qed.

Lemma Lget_app : forall (A:Set) (a:A) l i,
Lget i (l ++ a :: nil) = if Arith.EqNat.beq_nat i (length l) then Some a else Lget i l.
Proof.
induction l;simpl Lget;simpl length.
intros [ | i];simpl;reflexivity.
intros [ | i];simpl.
reflexivity.
auto.
Qed.

Lemma Lget_app_Some : forall (A:Set) l delta i (a: A),
Lget i l = Some a ->
Lget i (l ++ delta) = Some a.
induction l;destruct i;simpl;try congruence;auto.
Qed.

Section Store.

Variable A:Type.

Inductive Poption : Type:=
  PSome : A -> Poption
| PNone : Poption.

Inductive Tree : Type :=
   Tempty : Tree
 | Branch0 : Tree -> Tree -> Tree
 | Branch1 : A -> Tree -> Tree -> Tree.

Fixpoint Tget (p:positive) (T:Tree) {struct p} : Poption :=
  match T with
    Tempty => PNone
  | Branch0 T1 T2 =>
    match p with
      xI pp => Tget pp T2
    | xO pp => Tget pp T1
    | xH => PNone
    end
  | Branch1 a T1 T2 =>
    match p with
      xI pp => Tget pp T2
    | xO pp => Tget pp T1
    | xH => PSome a
    end
end.

Fixpoint Tadd (p:positive) (a:A) (T:Tree) {struct p}: Tree :=
 match T with
   | Tempty =>
       match p with
       | xI pp => Branch0 Tempty (Tadd pp a Tempty)
       | xO pp => Branch0 (Tadd pp a Tempty) Tempty
       | xH => Branch1 a Tempty Tempty
       end
   | Branch0 T1 T2 =>
       match p with
       | xI pp => Branch0 T1 (Tadd pp a T2)
       | xO pp => Branch0 (Tadd pp a T1) T2
       | xH => Branch1 a T1 T2
       end
   | Branch1 b T1 T2 =>
       match p with
       | xI pp => Branch1 b T1 (Tadd pp a T2)
       | xO pp => Branch1 b (Tadd pp a T1) T2
       | xH => Branch1 a T1 T2
       end
   end.

Definition mkBranch0 (T1 T2:Tree) :=
  match T1,T2 with
    Tempty ,Tempty => Tempty
  | _,_ => Branch0 T1 T2
  end.

Fixpoint Tremove (p:positive) (T:Tree) {struct p}: Tree :=
   match T with
      | Tempty => Tempty
      | Branch0 T1 T2 =>
        match p with
        | xI pp => mkBranch0 T1 (Tremove pp T2)
        | xO pp => mkBranch0 (Tremove pp T1) T2
        | xH => T
        end
      | Branch1 b T1 T2 =>
        match p with
        | xI pp => Branch1 b T1 (Tremove pp T2)
        | xO pp => Branch1 b (Tremove pp T1) T2
        | xH => mkBranch0 T1 T2
        end
      end.


Theorem Tget_Tempty: forall (p : positive), Tget p (Tempty) = PNone.
destruct p;reflexivity.
Qed.

Theorem Tget_Tadd: forall i j a T,
       Tget i (Tadd j a T) =
       match (i ?= j) with
         Eq => PSome a
       | Lt => Tget i T
       | Gt => Tget i T
       end.
Proof.
intros i j.
case_eq (i ?= j).
intro H;rewrite (Pos.compare_eq _ _ H);intros a;clear i H.
induction j;destruct T;simpl;try (apply IHj);congruence.
unfold Pos.compare.
generalize i;clear i;induction j;destruct T;simpl in H|-*;
destruct i;simpl;try rewrite (IHj _ H);try (destruct i;simpl;congruence);reflexivity|| congruence.
unfold Pos.compare.
generalize i;clear i;induction j;destruct T;simpl in H|-*;
destruct i;simpl;try rewrite (IHj _ H);try (destruct i;simpl;congruence);reflexivity|| congruence.
Qed.

Record Store : Type :=
mkStore  {index:positive;contents:Tree}.

Definition empty := mkStore xH Tempty.

Definition push a  S :=
mkStore (Pos.succ (index S)) (Tadd (index S) a (contents S)).

Definition get i S := Tget i (contents S).

Lemma get_empty : forall i, get i empty = PNone.
intro i; case i; unfold empty,get; simpl;reflexivity.
Qed.

Inductive Full : Store -> Type:=
    F_empty : Full empty
  | F_push : forall a S, Full S -> Full (push a S).

Theorem get_Full_Gt : forall S, Full S ->
       forall i, (i ?= index S) = Gt -> get i S = PNone.
Proof.
intros S W;induction W.
unfold empty,index,get,contents;intros;apply Tget_Tempty.
unfold index,get,push. simpl @contents.
intros i e;rewrite Tget_Tadd.
rewrite (Gt_Psucc _ _ e).
unfold get in IHW.
apply IHW;apply Gt_Psucc;assumption.
Qed.

Theorem get_Full_Eq : forall S, Full S -> get (index S) S = PNone.
intros [index0 contents0] F.
case F.
unfold empty,index,get,contents;intros;apply Tget_Tempty.
unfold push,index,get;simpl @contents.
intros a S.
rewrite Tget_Tadd.
rewrite Psucc_Gt.
intro W.
change (get (Pos.succ (index S)) S =PNone).
apply get_Full_Gt; auto.
apply Psucc_Gt.
Qed.

Theorem get_push_Full :
  forall i a S, Full S ->
  get i (push a S) =
  match (i ?= index S) with
    Eq => PSome a
  | Lt => get i S
  | Gt => PNone
end.
Proof.
intros i a S F.
case_eq (i ?= index S).
intro e;rewrite (Pos.compare_eq _ _ e).
destruct S;unfold get,push,index;simpl @contents;rewrite Tget_Tadd.
rewrite Pos.compare_refl;reflexivity.
intros;destruct S;unfold get,push,index;simpl @contents;rewrite Tget_Tadd.
simpl @index in H;rewrite H;reflexivity.
intro H;generalize H;clear H.
unfold get,push;simpl.
rewrite Tget_Tadd;intro e;rewrite e.
change (get i S=PNone).
apply get_Full_Gt;auto.
Qed.

Lemma Full_push_compat : forall i a S, Full S ->
forall x, get i S = PSome x ->
 get i (push a S) = PSome x.
Proof.
intros i a S F x H.
case_eq (i ?= index S);intro test.
rewrite (Pos.compare_eq _ _ test) in H.
rewrite (get_Full_Eq _ F) in H;congruence.
rewrite <- H.
rewrite (get_push_Full i a).
rewrite test;reflexivity.
assumption.
rewrite (get_Full_Gt _ F) in H;congruence.
Qed.

Lemma Full_index_one_empty : forall S, Full S -> index S = 1 -> S=empty.
intros [ind cont] F one; inversion F.
reflexivity.
simpl @index in one;assert (h:=Pos.succ_not_1 (index S)).
congruence.
Qed.

Lemma push_not_empty: forall a S, (push a S) <> empty.
intros a [ind cont];unfold push,empty.
intros [= H%Pos.succ_not_1]. assumption.
Qed.

Fixpoint In (x:A) (S:Store) (F:Full S) {struct F}: Prop :=
match F with
F_empty => False
| F_push a SS FF => x=a \/ In x SS FF
end.

Lemma get_In : forall (x:A) (S:Store) (F:Full S) i ,
get i S = PSome x -> In x S F.
induction F.
intro i;rewrite get_empty; congruence.
intro i;rewrite get_push_Full;trivial.
case_eq (i ?= index S);simpl.
left;congruence.
right;eauto.
congruence.
Qed.

End Store.

Arguments PNone [A].
Arguments PSome [A] _.

Arguments Tempty [A].
Arguments Branch0 [A] _ _.
Arguments Branch1 [A] _ _ _.

Arguments Tget [A] p T.
Arguments Tadd [A] p a T.

Arguments Tget_Tempty [A] p.
Arguments Tget_Tadd [A] i j a T.

Arguments mkStore [A] index contents.
Arguments index [A] s.
Arguments contents [A] s.

Arguments empty [A].
Arguments get [A] i S.
Arguments push [A] a S.

Arguments get_empty [A] i.
Arguments get_push_Full [A] i a S _.

Arguments Full [A] _.
Arguments F_empty [A].
Arguments F_push [A] a S _.
Arguments In [A] x S F.

Section Map.

Variables A B:Set.

Variable f: A -> B.

Fixpoint Tmap (T: Tree A) : Tree B :=
match T with
Tempty => Tempty
| Branch0 t1 t2 => Branch0 (Tmap t1) (Tmap t2)
| Branch1 a t1 t2 => Branch1 (f a) (Tmap t1) (Tmap t2)
end.

Lemma Tget_Tmap: forall T i,
Tget i (Tmap T)= match Tget i T with PNone => PNone
| PSome a => PSome (f a) end.
induction T;intro i;case i;simpl;auto.
Defined.

Lemma Tmap_Tadd: forall i a T,
Tmap (Tadd i a T) = Tadd i (f a) (Tmap T).
induction i;intros a T;case T;simpl;intros;try (rewrite IHi);simpl;reflexivity.
Defined.

Definition map (S:Store A) : Store B :=
mkStore (index S) (Tmap (contents S)).

Lemma get_map: forall i S,
get i (map S)= match get i S with PNone => PNone
| PSome a => PSome (f a) end.
destruct S;unfold get,map,contents,index;apply Tget_Tmap.
Defined.

Lemma map_push: forall a S,
map (push a S) = push (f a) (map S).
intros a S.
case S.
unfold push,map,contents,index.
intros;rewrite Tmap_Tadd;reflexivity.
Defined.

Theorem Full_map : forall S, Full S -> Full (map S).
intros S F.
induction F.
exact F_empty.
rewrite map_push;constructor 2;assumption.
Defined.

End Map.

Arguments Tmap [A B] f T.
Arguments map [A B] f S.
Arguments Full_map [A B f] S _.

Notation "hyps \ A" := (push A hyps) (at level 72,left associativity).
