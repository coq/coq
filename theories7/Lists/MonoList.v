(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** THIS IS A OLD CONTRIB. IT IS NO LONGER MAINTAINED ***)

Require Le.

Parameter List_Dom:Set.
Definition A := List_Dom.

Inductive list : Set := nil : list | cons : A -> list -> list.

Fixpoint app [l:list] : list -> list 
      := [m:list]<list>Cases l of
                           nil =>  m 
                       | (cons a l1) => (cons a (app l1 m)) 
                   end.


Lemma app_nil_end : (l:list)(l=(app l nil)).
Proof. 
	Intro l ; Elim l ; Simpl ; Auto.
        Induction 1; Auto.
Qed.
Hints Resolve app_nil_end : list v62.

Lemma app_ass : (l,m,n : list)(app (app l m) n)=(app l (app m n)).
Proof. 
	Intros l m n ; Elim l ; Simpl ; Auto with list.
	Induction 1; Auto with list.
Qed.
Hints Resolve app_ass : list v62.

Lemma ass_app : (l,m,n : list)(app l (app m n))=(app (app l m) n).
Proof. 
	Auto with list.
Qed.
Hints Resolve ass_app : list v62.

Definition tail := 
    [l:list] <list>Cases l of  (cons _ m) => m | _ => nil end : list->list.
                   

Lemma nil_cons : (a:A)(m:list)~nil=(cons a m).
  Intros; Discriminate.
Qed.

(****************************************)
(* Length of lists                      *)
(****************************************)

Fixpoint length [l:list] : nat 
   := <nat>Cases l of (cons _ m) => (S (length m)) | _ => O end.

(******************************)
(* Length order of lists      *)
(******************************)

Section length_order.
Definition lel := [l,m:list](le (length l) (length m)).

Hints Unfold lel : list.

Variables a,b:A.
Variables l,m,n:list.

Lemma lel_refl : (lel l l).
Proof. 
	Unfold lel ; Auto with list.
Qed.

Lemma lel_trans : (lel l m)->(lel m n)->(lel l n).
Proof. 
	Unfold lel ; Intros.
        Apply le_trans with (length m) ; Auto with list.
Qed.

Lemma lel_cons_cons : (lel l m)->(lel (cons a l) (cons b m)).
Proof. 
	Unfold lel ; Simpl ; Auto with list arith.
Qed.

Lemma lel_cons : (lel l m)->(lel l (cons b m)).
Proof. 
	Unfold lel ; Simpl ; Auto with list arith.
Qed.

Lemma lel_tail : (lel (cons a l) (cons b m)) -> (lel l m).
Proof. 
	Unfold lel ; Simpl ; Auto with list arith.
Qed.

Lemma lel_nil : (l':list)(lel l' nil)->(nil=l').
Proof. 
	Intro l' ; Elim l' ; Auto with list arith.
	Intros a' y H H0.
	(*  <list>nil=(cons a' y)
	    ============================
	      H0 : (lel (cons a' y) nil)
	      H : (lel y nil)->(<list>nil=y)
	      y : list
	      a' : A
	      l' : list *)
	Absurd (le (S (length y)) O); Auto with list arith.
Qed.
End length_order.

Hints Resolve lel_refl lel_cons_cons lel_cons lel_nil lel_nil nil_cons : list v62.

Fixpoint In  [a:A;l:list] : Prop :=
      Cases l of
         nil => False 
      | (cons b m) => (b=a)\/(In a m)
      end.

Lemma in_eq : (a:A)(l:list)(In a (cons a l)).
Proof. 
	Simpl ; Auto with list.
Qed.
Hints Resolve in_eq : list v62.

Lemma in_cons : (a,b:A)(l:list)(In b l)->(In b (cons a l)).
Proof. 
	Simpl ; Auto with list.
Qed.
Hints Resolve in_cons : list v62.

Lemma in_app_or : (l,m:list)(a:A)(In a (app l m))->((In a l)\/(In a m)).
Proof. 
	Intros l m a.
	Elim l ; Simpl ; Auto with list.
	Intros a0 y H H0.
	(*  ((<A>a0=a)\/(In a y))\/(In a m)
	    ============================
	      H0 : (<A>a0=a)\/(In a (app y m))
	      H : (In a (app y m))->((In a y)\/(In a m))
	      y : list
	      a0 : A
	      a : A
	      m : list
	      l : list *)
	Elim H0 ; Auto with list.
	Intro H1.
	(*  ((<A>a0=a)\/(In a y))\/(In a m)
	    ============================
	      H1 : (In a (app y m)) *)
	Elim (H H1) ; Auto with list.
Qed.
Hints Immediate in_app_or : list v62.

Lemma in_or_app : (l,m:list)(a:A)((In a l)\/(In a m))->(In a (app l m)).
Proof. 
	Intros l m a.
	Elim l ; Simpl ; Intro H.
	(* 1 (In a m)
	    ============================
	      H : False\/(In a m)
	      a : A
	      m : list
	      l : list *)
	Elim H ; Auto with list ; Intro H0.
	(*  (In a m)
	    ============================
	      H0 : False *)
	Elim H0. (* subProof completed *)
	Intros y H0 H1.
	(*  2 (<A>H=a)\/(In a (app y m))
	    ============================
	      H1 : ((<A>H=a)\/(In a y))\/(In a m)
	      H0 : ((In a y)\/(In a m))->(In a (app y m))
	      y : list *)
	Elim H1 ; Auto 4 with list.
	Intro H2.
	(*  (<A>H=a)\/(In a (app y m))
	    ============================
	      H2 : (<A>H=a)\/(In a y) *)
	Elim H2 ; Auto with list.
Qed.
Hints Resolve in_or_app : list v62.

Definition incl := [l,m:list](a:A)(In a l)->(In a m).

Hints Unfold  incl : list v62.

Lemma incl_refl : (l:list)(incl l l).
Proof. 
	Auto with list.
Qed.
Hints Resolve incl_refl : list v62.

Lemma incl_tl : (a:A)(l,m:list)(incl l m)->(incl l (cons a m)).
Proof. 
	Auto with list.
Qed.
Hints Immediate incl_tl : list v62.

Lemma incl_tran : (l,m,n:list)(incl l m)->(incl m n)->(incl l n).
Proof. 
	Auto with list.
Qed.

Lemma incl_appl : (l,m,n:list)(incl l n)->(incl l (app n m)).
Proof. 
	Auto with list.
Qed.
Hints Immediate incl_appl : list v62.

Lemma incl_appr : (l,m,n:list)(incl l n)->(incl l (app m n)).
Proof. 
	Auto with list.
Qed.
Hints Immediate incl_appr : list v62.

Lemma incl_cons : (a:A)(l,m:list)(In a m)->(incl l m)->(incl (cons a l) m).
Proof. 
	Unfold incl ; Simpl ; Intros a l m H H0 a0 H1.
	(*  (In a0 m)
	    ============================
	      H1 : (<A>a=a0)\/(In a0 l)
	      a0 : A
	      H0 : (a:A)(In a l)->(In a m)
	      H : (In a m)
	      m : list
	      l : list
	      a : A *)
	Elim H1.
	(*  1 (<A>a=a0)->(In a0 m) *)
	Elim H1 ; Auto with list ; Intro H2.
	(*  (<A>a=a0)->(In a0 m)
	    ============================
	      H2 : <A>a=a0 *)
	Elim H2 ; Auto with list. (* solves subgoal *)
	(*  2 (In a0 l)->(In a0 m) *)
	Auto with list.
Qed.
Hints Resolve incl_cons : list v62.

Lemma incl_app : (l,m,n:list)(incl l n)->(incl m n)->(incl (app l m) n).
Proof. 
	Unfold incl ; Simpl ; Intros l m n H H0 a H1.
	(*  (In a n)
	    ============================
	      H1 : (In a (app l m))
	      a : A
	      H0 : (a:A)(In a m)->(In a n)
	      H : (a:A)(In a l)->(In a n)
	      n : list
	      m : list
	      l : list *)
	Elim (in_app_or l m a) ; Auto with list.
Qed.
Hints Resolve incl_app : list v62.
