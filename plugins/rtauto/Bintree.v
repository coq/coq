(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export List.
Require Export BinPos.

Unset Boxed Definitions.

Open Scope positive_scope.

Ltac clean := try (simpl; congruence).
Ltac caseq t := generalize (refl_equal t); pattern t at -1; case t.

Functional Scheme Pcompare_ind := Induction for Pcompare Sort Prop.

Lemma Gt_Eq_Gt : forall p q cmp,
       (p ?= q) Eq = Gt -> (p ?= q) cmp = Gt.
apply (Pcompare_ind (fun p q cmp _ => (p ?= q) Eq = Gt -> (p ?= q) cmp = Gt));
simpl;auto;congruence.
Qed.

Lemma Gt_Lt_Gt : forall p q cmp,
       (p ?= q) Lt = Gt -> (p ?= q) cmp = Gt.
apply (Pcompare_ind (fun p q cmp _ => (p ?= q) Lt = Gt -> (p ?= q) cmp = Gt));
simpl;auto;congruence.
Qed.

Lemma Gt_Psucc_Eq: forall p q,
  (p ?= Psucc q) Gt = Gt -> (p ?= q) Eq = Gt.
intros p q;generalize p;clear p;induction q;destruct p;simpl;auto;try congruence.
intro;apply Gt_Eq_Gt;auto.
apply Gt_Lt_Gt.
Qed.

Lemma Eq_Psucc_Gt: forall p q,
  (p ?= Psucc q) Eq = Eq -> (p ?= q) Eq = Gt.
intros p q;generalize p;clear p;induction q;destruct p;simpl;auto;try congruence.
intro H;elim (Pcompare_not_Eq p (Psucc q));tauto.
intro H;apply Gt_Eq_Gt;auto.
intro H;rewrite Pcompare_Eq_eq with p q;auto.
generalize q;clear q IHq p H;induction q;simpl;auto.
intro H;elim (Pcompare_not_Eq p q);tauto.
Qed.

Lemma Gt_Psucc_Gt : forall n p cmp cmp0,
 (n?=p) cmp = Gt -> (Psucc n?=p) cmp0 = Gt.
induction n;intros [ | p | p];simpl;try congruence.
intros; apply IHn with cmp;trivial.
intros; apply IHn with Gt;trivial.
intros;apply Gt_Lt_Gt;trivial.
intros [ | | ] _ H.
apply Gt_Eq_Gt;trivial.
apply Gt_Lt_Gt;trivial.
trivial.
Qed.

Lemma Gt_Psucc: forall p q,
       (p ?= Psucc q) Eq = Gt -> (p ?= q) Eq = Gt.
intros p q;generalize p;clear p;induction q;destruct p;simpl;auto;try congruence.
apply Gt_Psucc_Eq.
intro;apply Gt_Eq_Gt;apply IHq;auto.
apply Gt_Eq_Gt.
apply Gt_Lt_Gt.
Qed.

Lemma Psucc_Gt : forall p,
       (Psucc p ?= p) Eq = Gt.
induction p;simpl.
apply Gt_Eq_Gt;auto.
generalize p;clear p IHp.
induction p;simpl;auto.
reflexivity.
Qed.

Fixpoint pos_eq (m n:positive) {struct m} :bool :=
match m, n with
  xI mm, xI nn => pos_eq mm nn
| xO mm, xO nn => pos_eq mm nn
| xH, xH => true
| _, _ => false
end.

Theorem pos_eq_refl : forall m n, pos_eq m n = true -> m = n.
induction m;simpl;intro n;destruct n;congruence ||
(intro e;apply f_equal with positive;auto).
Defined.

Theorem refl_pos_eq : forall m, pos_eq m m = true.
induction m;simpl;auto.
Qed.

Definition pos_eq_dec (m n:positive) :{m=n}+{m<>n} .
fix 1;intros [mm|mm|] [nn|nn|];try (right;congruence).
case (pos_eq_dec mm nn).
intro e;left;apply (f_equal xI e).
intro ne;right;congruence.
case (pos_eq_dec mm nn).
intro e;left;apply (f_equal xO e).
intro ne;right;congruence.
left;reflexivity.
Defined.

Theorem pos_eq_dec_refl : forall m, pos_eq_dec m m = left _ (refl_equal m).
fix 1;intros [mm|mm|].
simpl; rewrite  pos_eq_dec_refl; reflexivity.
simpl; rewrite  pos_eq_dec_refl; reflexivity.
reflexivity.
Qed.

Theorem pos_eq_dec_ex : forall m n,
 pos_eq m n =true -> exists h:m=n,
 pos_eq_dec m n = left _ h.
fix 1;intros [mm|mm|] [nn|nn|];try (simpl;congruence).
simpl;intro e.
elim (pos_eq_dec_ex _ _ e).
intros x ex; rewrite ex.
exists (f_equal xI x).
reflexivity.
simpl;intro e.
elim (pos_eq_dec_ex _ _ e).
intros x ex; rewrite ex.
exists (f_equal xO x).
reflexivity.
simpl.
exists (refl_equal xH).
reflexivity.
Qed.

Fixpoint nat_eq (m n:nat) {struct m}: bool:=
match m, n with
O,O => true
| S mm,S nn => nat_eq mm nn
| _,_ => false
end.

Theorem nat_eq_refl : forall m n, nat_eq m n = true -> m = n.
induction m;simpl;intro n;destruct n;congruence ||
(intro e;apply f_equal with nat;auto).
Defined.

Theorem refl_nat_eq : forall n, nat_eq n n = true.
induction n;simpl;trivial.
Defined.

Fixpoint Lget (A:Set) (n:nat) (l:list A) {struct l}:option A :=
match l with nil => None
| x::q =>
match n with O => Some x
| S m => Lget A m q
end end .

Implicit Arguments Lget [A].

Lemma map_app : forall (A B:Set) (f:A -> B) l m,
List.map  f (l ++ m) = List.map  f  l ++ List.map  f  m.
induction l.
reflexivity.
simpl.
intro m ; apply f_equal with (list B);apply IHl.
Qed.

Lemma length_map : forall (A B:Set) (f:A -> B) l,
length (List.map  f l) = length l.
induction l.
reflexivity.
simpl; apply f_equal with nat;apply IHl.
Qed.

Lemma Lget_map : forall (A B:Set) (f:A -> B) i l,
Lget i (List.map  f l) =
match Lget i l with Some a =>
Some (f a) | None => None end.
induction i;intros [ | x l ] ;trivial.
simpl;auto.
Qed.

Lemma Lget_app : forall (A:Set) (a:A) l i,
Lget i (l ++ a :: nil) = if nat_eq i (length l) then Some a else Lget i l.
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
       match (i ?= j) Eq with
         Eq => PSome a
       | Lt => Tget i T
       | Gt => Tget i T
       end.
intros i j.
caseq ((i ?= j) Eq).
intro H;rewrite (Pcompare_Eq_eq _ _ H);intros a;clear i H.
induction j;destruct T;simpl;try (apply IHj);congruence.
generalize i;clear i;induction j;destruct T;simpl in H|-*;
destruct i;simpl;try rewrite (IHj _ H);try (destruct i;simpl;congruence);reflexivity|| congruence.
generalize i;clear i;induction j;destruct T;simpl in H|-*;
destruct i;simpl;try rewrite (IHj _ H);try (destruct i;simpl;congruence);reflexivity|| congruence.
Qed.

Record Store : Type :=
mkStore  {index:positive;contents:Tree}.

Definition empty := mkStore xH Tempty.

Definition push a  S :=
mkStore (Psucc (index S)) (Tadd (index S) a (contents S)).

Definition get i S := Tget i (contents S).

Lemma get_empty : forall i, get i empty = PNone.
intro i; case i; unfold empty,get; simpl;reflexivity.
Qed.

Inductive Full : Store -> Type:=
    F_empty : Full empty
  | F_push : forall a S, Full S -> Full (push a S).

Theorem get_Full_Gt : forall S, Full S ->
       forall i, (i ?= index S) Eq = Gt -> get i S = PNone.
intros S W;induction W.
unfold empty,index,get,contents;intros;apply Tget_Tempty.
unfold index,get,push;simpl contents.
intros i e;rewrite Tget_Tadd.
rewrite (Gt_Psucc _ _ e).
unfold get in IHW.
apply IHW;apply Gt_Psucc;assumption.
Qed.

Theorem get_Full_Eq : forall S, Full S -> get (index S) S = PNone.
intros [index0 contents0] F.
case F.
unfold empty,index,get,contents;intros;apply Tget_Tempty.
unfold index,get,push;simpl contents.
intros a S.
rewrite Tget_Tadd.
rewrite Psucc_Gt.
intro W.
change (get (Psucc (index S)) S =PNone).
apply get_Full_Gt; auto.
apply Psucc_Gt.
Qed.

Theorem get_push_Full :
  forall i a S, Full S ->
  get i (push a S) =
  match (i ?= index S) Eq with
    Eq => PSome a
  | Lt => get i S
  | Gt => PNone
end.
intros i a S F.
caseq ((i ?= index S) Eq).
intro e;rewrite (Pcompare_Eq_eq _ _ e).
destruct S;unfold get,push,index;simpl contents;rewrite Tget_Tadd.
rewrite Pcompare_refl;reflexivity.
intros;destruct S;unfold get,push,index;simpl contents;rewrite Tget_Tadd.
simpl index in H;rewrite H;reflexivity.
intro H;generalize H;clear H.
unfold get,push;simpl index;simpl contents.
rewrite Tget_Tadd;intro e;rewrite e.
change (get i S=PNone).
apply get_Full_Gt;auto.
Qed.

Lemma Full_push_compat : forall i a S, Full S ->
forall x, get i S = PSome x ->
 get i (push a S) = PSome x.
intros i a S F x H.
caseq ((i ?= index S) Eq);intro test.
rewrite (Pcompare_Eq_eq _ _ test) in H.
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
simpl index in one;assert (h:=Psucc_not_one (index S)).
congruence.
Qed.

Lemma push_not_empty: forall a S, (push a S) <> empty.
intros a [ind cont];unfold push,empty.
simpl;intro H;injection H; intros _ ; apply Psucc_not_one.
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
caseq ((i ?= index S) Eq);simpl.
left;congruence.
right;eauto.
congruence.
Qed.

End Store.

Implicit Arguments PNone [A].
Implicit Arguments PSome [A].

Implicit Arguments Tempty [A].
Implicit Arguments Branch0 [A].
Implicit Arguments Branch1 [A].

Implicit Arguments Tget [A].
Implicit Arguments Tadd [A].

Implicit Arguments Tget_Tempty [A].
Implicit Arguments Tget_Tadd [A].

Implicit Arguments mkStore [A].
Implicit Arguments index [A].
Implicit Arguments contents [A].

Implicit Arguments empty [A].
Implicit Arguments get [A].
Implicit Arguments push [A].

Implicit Arguments get_empty [A].
Implicit Arguments get_push_Full [A].

Implicit Arguments Full [A].
Implicit Arguments F_empty [A].
Implicit Arguments F_push [A].
Implicit Arguments In [A].

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

Implicit Arguments Tmap [A B].
Implicit Arguments map [A B].
Implicit Arguments Full_map [A B f].

Notation "hyps \ A" := (push A hyps) (at level 72,left associativity).
