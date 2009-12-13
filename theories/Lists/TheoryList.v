(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Some programs and results about lists following CAML Manual *)

Require Export List.
Set Implicit Arguments.

Local Notation "[ ]" := nil (at level 0).
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) (at level 0).

Section Lists.

Variable A : Type.

(**********************)
(** The null function *)
(**********************)

Definition Isnil (l:list A) : Prop := nil = l.

Lemma Isnil_nil : Isnil nil.
Proof.
red in |- *; auto.
Qed.
Hint Resolve Isnil_nil.

Lemma not_Isnil_cons : forall (a:A) (l:list A), ~ Isnil (a :: l).
Proof.
unfold Isnil in |- *.
intros; discriminate.
Qed.

Hint Resolve Isnil_nil not_Isnil_cons.

Lemma Isnil_dec : forall l:list A, {Isnil l} + {~ Isnil l}.
Proof.
intro l; case l; auto.
(*
Realizer (fun l => match l with
  | nil => true
  | _ => false
  end).
*)
Qed.

(************************)
(** The Uncons function *)
(************************)

Lemma Uncons :
 forall l:list A, {a : A &  {m : list A | a :: m = l}} + {Isnil l}.
Proof.
intro l; case l.
auto.
intros a m; intros; left; exists a; exists m; reflexivity.
(*
Realizer (fun l => match l with
  | nil => error
  | (cons a m) => value (a,m)
  end).
*)
Qed.

(********************************)
(** The head function           *)
(********************************)

Lemma Hd :
 forall l:list A, {a : A |  exists m : list A, a :: m = l} + {Isnil l}.
Proof.
intro l; case l.
auto.
intros a m; intros; left; exists a; exists m; reflexivity.
(*
Realizer (fun l => match l with
  | nil => error
  | (cons a m) => value a
  end).
*)
Qed.

Lemma Tl :
 forall l:list A,
   {m : list A | (exists a : A, a :: m = l) \/ Isnil l /\ Isnil m}.
Proof.
intro l; case l.
exists (nil (A:=A)); auto.
intros a m; intros; exists m; left; exists a; reflexivity.
(*
Realizer (fun l => match l with
  | nil => nil
  | (cons a m) => m
  end).
*)
Qed.

(****************************************)
(** Length of lists                     *)
(****************************************)

(* length is defined in List *)
Fixpoint Length_l (l:list A) (n:nat) : nat :=
  match l with
  | nil => n
  | _ :: m => Length_l m (S n)
  end.

(* A tail recursive version *)
Lemma Length_l_pf : forall (l:list A) (n:nat), {m : nat | n + length l = m}.
Proof.
induction l as [| a m lrec].
intro n; exists n; simpl in |- *; auto.
intro n; elim (lrec (S n)); simpl in |- *; intros.
exists x; transitivity (S (n + length m)); auto.
(*
Realizer Length_l.
*)
Qed.

Lemma Length : forall l:list A, {m : nat | length l = m}.
Proof.
intro l. apply (Length_l_pf l 0).
(*
Realizer (fun l -> Length_l_pf l O).
*)
Qed.

(*******************************)
(** Members of lists           *)
(*******************************)
Inductive In_spec (a:A) : list A -> Prop :=
  | in_hd : forall l:list A, In_spec a (a :: l)
  | in_tl : forall (l:list A) (b:A), In a l -> In_spec a (b :: l).
Hint Resolve in_hd in_tl.
Hint Unfold In.
Hint Resolve in_cons.

Theorem In_In_spec : forall (a:A) (l:list A), In a l <-> In_spec a l.
split.
elim l;
 [ intros; contradiction
 | intros; elim H0; [ intros; rewrite H1; auto | auto ] ].
intros; elim H; auto.
Qed.

Hypothesis eqA_dec : forall a b:A, {a = b} + {a <> b}.

Fixpoint mem (a:A) (l:list A) : bool :=
  match l with
  | nil => false
  | b :: m => if eqA_dec a b then true else mem a m
  end.

Hint Unfold In.
Lemma Mem : forall (a:A) (l:list A), {In a l} + {AllS (fun b:A => b <> a) l}.
Proof.
induction l.
auto.
elim (eqA_dec a a0).
auto.
simpl in |- *. elim IHl; auto.
(*
Realizer mem.
*)
Qed.

(*********************************)
(** Index of elements            *)
(*********************************)

Require Import Le.
Require Import Lt.

Inductive nth_spec : list A -> nat -> A -> Prop :=
  | nth_spec_O : forall (a:A) (l:list A), nth_spec (a :: l) 1 a
  | nth_spec_S :
      forall (n:nat) (a b:A) (l:list A),
        nth_spec l n a -> nth_spec (b :: l) (S n) a.
Hint Resolve nth_spec_O nth_spec_S.

Inductive fst_nth_spec : list A -> nat -> A -> Prop :=
  | fst_nth_O : forall (a:A) (l:list A), fst_nth_spec (a :: l) 1 a
  | fst_nth_S :
      forall (n:nat) (a b:A) (l:list A),
        a <> b -> fst_nth_spec l n a -> fst_nth_spec (b :: l) (S n) a.
Hint Resolve fst_nth_O fst_nth_S.

Lemma fst_nth_nth :
 forall (l:list A) (n:nat) (a:A), fst_nth_spec l n a -> nth_spec l n a.
Proof.
induction 1; auto.
Qed.
Hint Immediate fst_nth_nth.

Lemma nth_lt_O : forall (l:list A) (n:nat) (a:A), nth_spec l n a -> 0 < n.
Proof.
induction 1; auto.
Qed.

Lemma nth_le_length :
 forall (l:list A) (n:nat) (a:A), nth_spec l n a -> n <= length l.
Proof.
induction 1; simpl in |- *; auto with arith.
Qed.

Fixpoint Nth_func (l:list A) (n:nat) : Exc A :=
  match l, n with
  | a :: _, S O => value a
  | _ :: l', S (S p) => Nth_func l' (S p)
  | _, _ => error
  end.

Lemma Nth :
 forall (l:list A) (n:nat),
   {a : A | nth_spec l n a} + {n = 0 \/ length l < n}.
Proof.
induction l as [| a l IHl].
intro n; case n; simpl in |- *; auto with arith.
intro n; destruct n as [| [| n1]]; simpl in |- *; auto.
left; exists a; auto.
destruct (IHl (S n1)) as [[b]| o].
left; exists b; auto.
right; destruct o.
absurd (S n1 = 0); auto.
auto with arith.
(*
Realizer Nth_func.
*)
Qed.

Lemma Item :
 forall (l:list A) (n:nat), {a : A | nth_spec l (S n) a} + {length l <= n}.
Proof.
intros l n; case (Nth l (S n)); intro.
case s; intro a; left; exists a; auto.
right; case o; intro.
absurd (S n = 0); auto.
auto with arith.
Qed.

Require Import Minus.
Require Import DecBool.

Fixpoint index_p (a:A) (l:list A) : nat -> Exc nat :=
  match l with
  | nil => fun p => error
  | b :: m => fun p => ifdec (eqA_dec a b) (value p) (index_p a m (S p))
  end.

Lemma Index_p :
 forall (a:A) (l:list A) (p:nat),
   {n : nat | fst_nth_spec l (S n - p) a} + {AllS (fun b:A => a <> b) l}.
Proof.
induction l as [| b m irec].
auto.
intro p.
destruct (eqA_dec a b) as [e| e].
left; exists p.
destruct e; elim minus_Sn_m; trivial; elim minus_n_n; auto with arith.
destruct (irec (S p)) as [[n H]| ].
left; exists n; auto with arith.
elim minus_Sn_m; auto with arith.
apply lt_le_weak; apply lt_O_minus_lt; apply nth_lt_O with m a;
 auto with arith.
auto.
Qed.

Lemma Index :
 forall (a:A) (l:list A),
   {n : nat | fst_nth_spec l n a} + {AllS (fun b:A => a <> b) l}.

Proof.
intros a l; case (Index_p a l 1); auto.
intros [n P]; left; exists n; auto.
rewrite (minus_n_O n); trivial.
(*
Realizer (fun a l -> Index_p a l (S O)).
*)
Qed.

Section Find_sec.
Variables R P : A -> Prop.

Inductive InR : list A -> Prop :=
  | inR_hd : forall (a:A) (l:list A), R a -> InR (a :: l)
  | inR_tl : forall (a:A) (l:list A), InR l -> InR (a :: l).
Hint Resolve inR_hd inR_tl.

Definition InR_inv (l:list A) :=
  match l with
  | nil => False
  | b :: m => R b \/ InR m
  end.

Lemma InR_INV : forall l:list A, InR l -> InR_inv l.
Proof.
induction 1; simpl in |- *; auto.
Qed.

Lemma InR_cons_inv : forall (a:A) (l:list A), InR (a :: l) -> R a \/ InR l.
Proof.
intros a l H; exact (InR_INV H).
Qed.

Lemma InR_or_app : forall l m:list A, InR l \/ InR m -> InR (l ++ m).
Proof.
intros l m [| ].
induction 1; simpl in |- *; auto.
intro. induction l; simpl in |- *; auto.
Qed.

Lemma InR_app_or : forall l m:list A, InR (l ++ m) -> InR l \/ InR m.
Proof.
intros l m; elim l; simpl in |- *; auto.
intros b l' Hrec IAc; elim (InR_cons_inv IAc); auto.
intros; elim Hrec; auto.
Qed.

Hypothesis RS_dec : forall a:A, {R a} + {P a}.

Fixpoint find (l:list A) : Exc A :=
  match l with
  | nil => error
  | a :: m => ifdec (RS_dec a) (value a) (find m)
  end.

Lemma Find : forall l:list A, {a : A | In a l &  R a} + {AllS P l}.
Proof.
induction l as [| a m [[b H1 H2]| H]]; auto.
left; exists b; auto.
destruct (RS_dec a).
left; exists a; auto.
auto.
(*
Realizer find.
*)
Qed.

Variable B : Type.
Variable T : A -> B -> Prop.

Variable TS_dec : forall a:A, {c : B | T a c} + {P a}.

Fixpoint try_find (l:list A) : Exc B :=
  match l with
  | nil => error
  | a :: l1 =>
      match TS_dec a with
      | inleft (exist c _) => value c
      | inright _ => try_find l1
      end
  end.

Lemma Try_find :
 forall l:list A, {c : B |  exists2 a : A, In a l & T a c} + {AllS P l}.
Proof.
induction l as [| a m [[b H1]| H]].
auto.
left; exists b; destruct H1 as [a' H2 H3]; exists a'; auto.
destruct (TS_dec a) as [[c H1]| ].
left; exists c.
exists a; auto.
auto.
(*
Realizer try_find.
*)
Qed.

End Find_sec.

Section Assoc_sec.

Variable B : Type.
Fixpoint assoc (a:A) (l:list (A * B)) :
 Exc B :=
  match l with
  | nil => error
  | (a', b) :: m => ifdec (eqA_dec a a') (value b) (assoc a m)
  end.

Inductive AllS_assoc (P:A -> Prop) : list (A * B) -> Prop :=
  | allS_assoc_nil : AllS_assoc P nil
  | allS_assoc_cons :
      forall (a:A) (b:B) (l:list (A * B)),
        P a -> AllS_assoc P l -> AllS_assoc P ((a, b) :: l).

Hint Resolve allS_assoc_nil allS_assoc_cons.

(* The specification seems too weak: it is enough to return b if the
   list has at least an element (a,b); probably the intention is to have
   the specification

   (a:A)(l:(list A*B)){b:B|(In_spec (a,b) l)}+{(AllS_assoc [a':A]~(a=a') l)}.
*)

Lemma Assoc :
 forall (a:A) (l:list (A * B)), B + {AllS_assoc (fun a':A => a <> a') l}.
Proof.
induction l as [| [a' b] m assrec]. auto.
destruct (eqA_dec a a').
left; exact b.
destruct assrec as [b'| ].
left; exact b'.
right; auto.
(*
Realizer assoc.
*)
Qed.

End Assoc_sec.

End Lists.

Hint Resolve Isnil_nil not_Isnil_cons in_hd in_tl in_cons : datatypes.
Hint Immediate fst_nth_nth: datatypes.
