(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Set Implicit Arguments.
Require Import BinPos.
Require Import List.
Open Scope positive_scope.

Section LIST.
 Variable A : Type.
 Variable default : A.

 Definition hd l := match l with hd :: _ => hd | _ => default end. 

 Fixpoint jump (p:positive) (l:list A) {struct p} : list A :=
  match p with
  | xH => tail l
  | xO p => jump p (jump p l)
  | xI p  => jump p (jump p (tail l))
  end.

 Fixpoint nth (p:positive) (l:list A) {struct p} : A:=
  match p with
  | xH => hd l
  | xO p => nth p (jump p l)
  | xI p => nth p (jump p (tail l))
  end. 

 Fixpoint rev_append (rev l : list A) {struct l} : list A :=
  match l with
  | nil => rev
  | (cons h t) => rev_append (cons h rev) t 
  end.
 
 Definition rev l : list A := rev_append nil l.

 Lemma jump_tl : forall j l, tail (jump j l) = jump j (tail l).
 Proof. 
  induction j;simpl;intros.
  repeat rewrite IHj;trivial.
  repeat rewrite IHj;trivial.
  trivial.
 Qed.

 Lemma jump_Psucc : forall j l, 
  (jump (Psucc j) l) = (jump 1 (jump j l)).
 Proof.
  induction j;simpl;intros.
  repeat rewrite IHj;simpl;repeat rewrite jump_tl;trivial.
  repeat rewrite jump_tl;trivial.
  trivial.
 Qed.

 Lemma jump_Pplus : forall i j l, 
  (jump (i + j) l) = (jump i (jump j l)).
 Proof.
  induction i;intros.
  rewrite xI_succ_xO;rewrite Pplus_one_succ_r.
  rewrite <- Pplus_diag;repeat rewrite <- Pplus_assoc.
  repeat rewrite IHi.
  rewrite Pplus_comm;rewrite <- Pplus_one_succ_r;rewrite jump_Psucc;trivial.
  rewrite <- Pplus_diag;repeat rewrite <- Pplus_assoc.
  repeat rewrite IHi;trivial.
  rewrite Pplus_comm;rewrite <- Pplus_one_succ_r;rewrite jump_Psucc;trivial.
 Qed.

 Lemma jump_Pdouble_minus_one : forall i l,
  (jump (Pdouble_minus_one i) (tail l)) = (jump i (jump i l)).
 Proof.
  induction i;intros;simpl.
  repeat rewrite jump_tl;trivial.
  rewrite IHi. do 2 rewrite <- jump_tl;rewrite IHi;trivial.
  trivial.
 Qed.

 
 Lemma nth_jump : forall p l, nth p (tail l) = hd (jump p l).
 Proof.
  induction p;simpl;intros.
  rewrite <-jump_tl;rewrite IHp;trivial.
  rewrite <-jump_tl;rewrite IHp;trivial.
  trivial.
 Qed.

 Lemma nth_Pdouble_minus_one :
  forall p l, nth (Pdouble_minus_one p) (tail l) = nth p (jump p l).
 Proof.
  induction p;simpl;intros.
  repeat rewrite jump_tl;trivial.
  rewrite jump_Pdouble_minus_one.
  repeat rewrite <- jump_tl;rewrite IHp;trivial.
  trivial.
 Qed.

End LIST.
Notation list := List.list.
Notation tail := List.tail.
Notation cons := List.cons.
Notation nil := List.nil.

Ltac list_fold_right fcons fnil l :=
  match l with
  | (cons ?x ?tl) => fcons x ltac:(list_fold_right fcons fnil tl)
  | nil => fnil
  end.

Ltac list_fold_left fcons fnil l :=
  match l with
  | (cons ?x ?tl) => list_fold_left fcons ltac:(fcons x fnil) tl
  | nil => fnil
  end.

Ltac list_iter f l :=
  match l with
  | (cons ?x ?tl) => f x; list_iter f tl
  | nil => idtac
  end.

Ltac list_iter_gen seq f l :=
  match l with
  | (cons ?x ?tl) =>
      let t1 _ := f x in
      let t2 _ := list_iter_gen seq f tl in
      seq t1 t2
  | nil => idtac
  end.

Ltac AddFvTail a l :=
 match l with
 | nil          => constr:(cons a l)
 | (cons a _)   => l
 | (cons ?x ?l) => let l' := AddFvTail a l in constr:(cons x l')
 end.

Ltac Find_at a l :=
 let rec find n l :=
   match l with
   | nil => fail 100 "anomaly: Find_at"
   | (cons a _) => eval compute in n
   | (cons _ ?l) => find (Psucc n) l
   end
 in find 1%positive l.

Ltac check_is_list t :=
  match t with
  | cons _ ?l => check_is_list l
  | nil => idtac
  | _ => fail 100 "anomaly: failed to build a canonical list"
  end.

Ltac check_fv l :=
  check_is_list l;
  match type of l with 
  | list _ => idtac
  | _ => fail 100 "anomaly: built an ill-typed list"
  end.
