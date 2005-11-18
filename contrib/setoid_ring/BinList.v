Set Implicit Arguments.
Require Import BinPos.
Open Scope positive_scope.


Section LIST.

 Variable A:Type.
 Variable default:A.

 Inductive list : Type :=
  | nil : list
  | cons : A -> list -> list.
  
 Infix "::" := cons (at level 60, right associativity).

 Definition hd l := match l with hd :: _ => hd | _ => default end. 

 Definition tl l := match l with _ :: tl => tl | _ => nil end. 

 Fixpoint jump (p:positive) (l:list) {struct p} : list :=
  match p with
  | xH => tl l
  | xO p => jump p (jump p l)
  | xI p  => jump p (jump p (tl l))
  end.

 Fixpoint nth (p:positive) (l:list) {struct p} : A:=
  match p with
  | xH => hd l
  | xO p => nth p (jump p l)
  | xI p => nth p (jump p (tl l))
  end. 

 Fixpoint rev_append (rev l : list) {struct l} : list :=
  match l with
  | nil => rev
  | (cons h t) => rev_append (cons h rev) t 
  end.
 
 Definition rev l : list := rev_append nil l.

 Lemma jump_tl : forall j l, tl (jump j l) = jump j (tl l).
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
  (jump (Pdouble_minus_one i) (tl l)) = (jump i (jump i l)).
 Proof.
  induction i;intros;simpl.
  repeat rewrite jump_tl;trivial.
  rewrite IHi. do 2 rewrite <- jump_tl;rewrite IHi;trivial.
  trivial.
 Qed.

 
 Lemma nth_jump : forall p l, nth p (tl l) = hd (jump p l).
 Proof.
  induction p;simpl;intros.
  rewrite <-jump_tl;rewrite IHp;trivial.
  rewrite <-jump_tl;rewrite IHp;trivial.
  trivial.
 Qed.

 Lemma nth_Pdouble_minus_one :
  forall p l, nth (Pdouble_minus_one p) (tl l) = nth p (jump p l).
 Proof.
  induction p;simpl;intros.
  repeat rewrite jump_tl;trivial.
  rewrite jump_Pdouble_minus_one.
  repeat rewrite <- jump_tl;rewrite IHp;trivial.
  trivial.
 Qed.

End LIST.
