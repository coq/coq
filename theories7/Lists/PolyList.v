(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Le.


Section Lists.

Variable A : Set.

Set Implicit Arguments.

Inductive list : Set := nil : list | cons : A -> list -> list.

Infix "::" cons (at level 7, right associativity) : list_scope
  V8only (at level 60, right associativity).

Open Scope list_scope.

(*************************)
(** Discrimination       *)
(*************************)

Lemma nil_cons : (a:A)(m:list)~(nil=(cons a m)).
Proof. 
  Intros; Discriminate.
Qed.

(*************************)
(** Concatenation        *)
(*************************)

Fixpoint app [l:list] : list -> list 
      := [m:list]Cases l of
                   nil         => m 
                 | (cons a l1) => (cons a (app l1 m))
                 end.

Infix RIGHTA 7 "^" app : list_scope
  V8only RIGHTA 60 "++".

Lemma app_nil_end : (l:list)l=(l^nil).
Proof. 
	NewInduction l ; Simpl ; Auto.
        Rewrite <- IHl; Auto.
Qed.
Hints Resolve app_nil_end.

Tactic Definition now_show c := Change c.
V7only [Tactic Definition NowShow := now_show.].

Lemma app_ass : (l,m,n : list)((l^m)^ n)=(l^(m^n)).
Proof. 
	Intros. NewInduction l ; Simpl ; Auto.
        NowShow '(cons a (app (app l m) n))=(cons a (app l (app m n))).
	Rewrite <- IHl; Auto.
Qed.
Hints Resolve app_ass.

Lemma ass_app : (l,m,n : list)(l^(m^n))=((l^m)^n).
Proof. 
	Auto.
Qed.
Hints Resolve ass_app.

Lemma app_comm_cons : (x,y:list)(a:A) (cons a (x^y))=((cons a x)^y).
Proof.
 Auto.
Qed.

Lemma app_eq_nil: (x,y:list) (x^y)=nil -> x=nil /\ y=nil.
Proof.
  NewDestruct x;NewDestruct y;Simpl;Auto.
  Intros H;Discriminate H.
  Intros;Discriminate H.
Qed.

Lemma app_cons_not_nil: (x,y:list)(a:A)~nil=(x^(cons a y)).
Proof.
Unfold not .
  NewDestruct x;Simpl;Intros.
  Discriminate H.
  Discriminate H.
Qed.

Lemma app_eq_unit:(x,y:list)(a:A)
     (x^y)=(cons a nil)-> (x=nil)/\ y=(cons a nil) \/ x=(cons a nil)/\ y=nil.

Proof.
  NewDestruct x;NewDestruct y;Simpl.
  Intros a H;Discriminate H.
  Left;Split;Auto.
  Right;Split;Auto.
  Generalize H .
  Generalize (app_nil_end  l) ;Intros E.
  Rewrite <- E;Auto.
  Intros.
  Injection H.
  Intro.
  Cut  nil=(l^(cons a0 l0));Auto.
  Intro.
  Generalize (app_cons_not_nil H1); Intro.
  Elim H2.
Qed.

Lemma app_inj_tail : (x,y:list)(a,b:A)
   (x^(cons a nil))=(y^(cons b nil)) -> x=y /\ a=b.
Proof.
  NewInduction x as [|x l IHl];NewDestruct y;Simpl;Auto.
  Intros a b H.
  Injection H.
  Auto.
  Intros a0 b H.
  Injection H;Intros.
  Generalize (app_cons_not_nil H0) ;NewDestruct 1.
  Intros a b H.
  Injection H;Intros.
  Cut   nil=(l^(cons a nil));Auto.
  Intro.
  Generalize (app_cons_not_nil H2) ;NewDestruct 1.
  Intros a0 b H.
  Injection H;Intros.
  NewDestruct (IHl l0 a0 b H0). 
  Split;Auto.
  Rewrite <- H1;Rewrite <- H2;Reflexivity.
Qed.

(*************************)
(** Head and tail        *)
(*************************)

Definition head :=
  [l:list]Cases l of
  | nil => Error
  | (cons x _) => (Value x)
  end.

Definition tail : list -> list :=
  [l:list]Cases l of
  | nil => nil 
  | (cons a m) => m
  end.

(****************************************)
(** Length of lists                     *)
(****************************************)

Fixpoint length [l:list] : nat 
   := Cases l of nil => O | (cons _ m) => (S (length m)) end.

(******************************)
(** Length order of lists     *)
(******************************)

Section length_order.
Definition lel := [l,m:list](le (length l) (length m)).

Variables a,b:A.
Variables l,m,n:list.

Lemma lel_refl : (lel l l).
Proof. 
	Unfold lel ; Auto with arith.
Qed.

Lemma lel_trans : (lel l m)->(lel m n)->(lel l n).
Proof. 
	Unfold lel ; Intros.
        NowShow '(le (length l) (length n)).
        Apply le_trans with (length m) ; Auto with arith.
Qed.

Lemma lel_cons_cons : (lel l m)->(lel (cons a l) (cons b m)).
Proof. 
	Unfold lel ; Simpl ; Auto with arith.
Qed.

Lemma lel_cons : (lel l m)->(lel l (cons b m)).
Proof. 
	Unfold lel ; Simpl ; Auto with arith.
Qed.

Lemma lel_tail : (lel (cons a l) (cons b m)) -> (lel l m).
Proof. 
	Unfold lel ; Simpl ; Auto with arith.
Qed.

Lemma lel_nil : (l':list)(lel l' nil)->(nil=l').
Proof. 
	Intro l' ; Elim l' ; Auto with arith.
	Intros a' y H H0.
        NowShow 'nil=(cons a' y).
	Absurd (le (S (length y)) O); Auto with arith.
Qed.
End length_order.

Hints Resolve lel_refl lel_cons_cons lel_cons lel_nil lel_nil nil_cons.

(*********************************)
(** The [In] predicate           *)
(*********************************)

Fixpoint In  [a:A;l:list] : Prop :=
      Cases l of nil => False | (cons b m) => (b=a)\/(In a m) end.

Lemma in_eq : (a:A)(l:list)(In a (cons a l)).
Proof. 
	Simpl ; Auto.
Qed.
Hints Resolve in_eq.

Lemma in_cons : (a,b:A)(l:list)(In b l)->(In b (cons a l)).
Proof. 
	Simpl ; Auto.
Qed.
Hints Resolve in_cons.

Lemma in_nil : (a:A)~(In a nil).
Proof.
  Unfold not; Intros a H; Inversion_clear H.
Qed.


Lemma in_inv : (a,b:A)(l:list)
               (In b (cons a l)) -> a=b \/ (In b l).
Proof.
 Intros a b l H ; Inversion_clear H ; Auto.
Qed.

Lemma In_dec : ((x,y:A){x=y}+{~x=y}) ->   (a:A)(l:list){(In a l)}+{~(In a l)}.

Proof.
  NewInduction l as [|a0 l IHl].
  Right; Apply in_nil.
  NewDestruct (H a0 a); Simpl; Auto.
  NewDestruct IHl; Simpl; Auto. 
  Right; Unfold not; Intros [Hc1 | Hc2]; Auto.
Qed.

Lemma in_app_or : (l,m:list)(a:A)(In a (l^m))->((In a l)\/(In a m)).
Proof. 
	Intros l m a.
	Elim l ; Simpl ; Auto.
	Intros a0 y H H0.
	NowShow '(a0=a\/(In a y))\/(In a m).
	Elim H0 ; Auto.
	Intro H1.
        NowShow '(a0=a\/(In a y))\/(In a m).
	Elim (H H1) ; Auto.
Qed.
Hints Immediate in_app_or.

Lemma in_or_app : (l,m:list)(a:A)((In a l)\/(In a m))->(In a (l^m)).
Proof. 
	Intros l m a.
	Elim l ; Simpl ; Intro H.
        NowShow '(In a m).
	Elim H ; Auto ; Intro H0.
	NowShow '(In a m).
	Elim H0. (* subProof completed *)
	Intros y H0 H1.
	NowShow 'H=a\/(In a (app y m)).
	Elim H1 ; Auto 4.
	Intro H2.
	NowShow 'H=a\/(In a (app y m)).
	Elim H2 ; Auto.
Qed.
Hints Resolve in_or_app.

(***************************)
(** Set inclusion on list  *)
(***************************)

Definition incl := [l,m:list](a:A)(In a l)->(In a m).
Hints Unfold  incl.

Lemma incl_refl : (l:list)(incl l l).
Proof. 
	Auto.
Qed.
Hints Resolve incl_refl.

Lemma incl_tl : (a:A)(l,m:list)(incl l m)->(incl l (cons a m)).
Proof. 
	Auto.
Qed.
Hints Immediate incl_tl.

Lemma incl_tran : (l,m,n:list)(incl l m)->(incl m n)->(incl l n).
Proof. 
	Auto.
Qed.

Lemma incl_appl : (l,m,n:list)(incl l n)->(incl l (n^m)).
Proof. 
	Auto.
Qed.
Hints Immediate incl_appl.

Lemma incl_appr : (l,m,n:list)(incl l n)->(incl l (m^n)).
Proof. 
	Auto.
Qed.
Hints Immediate incl_appr.

Lemma incl_cons : (a:A)(l,m:list)(In a m)->(incl l m)->(incl (cons a l) m).
Proof. 
	Unfold incl ; Simpl ; Intros a l m H H0 a0 H1.
        NowShow '(In a0 m).
	Elim H1.
	NowShow 'a=a0->(In a0 m).
	Elim H1 ; Auto ; Intro H2.
	NowShow 'a=a0->(In a0 m).
	Elim H2 ; Auto. (* solves subgoal *)
	NowShow '(In a0 l)->(In a0 m).
	Auto.
Qed.
Hints Resolve incl_cons.

Lemma incl_app : (l,m,n:list)(incl l n)->(incl m n)->(incl (l^m) n).
Proof. 
	Unfold incl ; Simpl ; Intros l m n H H0 a H1.
        NowShow '(In a n).
	Elim (in_app_or H1); Auto.
Qed.
Hints Resolve incl_app.

(**************************)
(** Nth element of a list *)
(**************************)

Fixpoint nth [n:nat; l:list] : A->A :=
  [default]Cases n l of
    O (cons x l') => x
  | O other => default
  | (S m) nil => default
  | (S m) (cons x t) => (nth m t default)
  end.

Fixpoint nth_ok [n:nat; l:list] : A->bool :=
  [default]Cases n l of
    O (cons x l') => true
  | O other => false
  | (S m) nil => false
  | (S m) (cons x t) => (nth_ok m t default)
  end.

Lemma nth_in_or_default :
  (n:nat)(l:list)(d:A){(In (nth n l d) l)}+{(nth n l d)=d}.
(* Realizer nth_ok. Program_all. *)
Proof. 
  Intros n l d; Generalize n; NewInduction l; Intro n0.
  Right; Case n0; Trivial.
  Case n0; Simpl.
  Auto.
  Intro n1; Elim (IHl n1); Auto.     
Qed.

Lemma nth_S_cons :
 (n:nat)(l:list)(d:A)(a:A)(In (nth n l d) l)
   ->(In (nth (S n) (cons a l) d) (cons a l)).
Proof. 
  Simpl; Auto.
Qed.

Fixpoint nth_error [l:list;n:nat] : (Exc A) :=
  Cases n l of
  | O (cons x _) => (Value x)
  | (S n) (cons _ l) => (nth_error l n)
  | _ _ => Error 
  end.

Definition nth_default : A -> list -> nat -> A :=
  [default,l,n]Cases (nth_error l n) of
  | (Some x) => x
  | None => default
  end.

Lemma nth_In :
  (n:nat)(l:list)(d:A)(lt n (length l))->(In (nth n l d) l).

Proof.
Unfold lt; NewInduction n as [|n hn]; Simpl.
NewDestruct l ; Simpl ;  [ Inversion 2 | Auto].
NewDestruct l as [|a l hl] ; Simpl.
Inversion 2.
Intros d ie ; Right ; Apply hn ; Auto with arith.
Qed.

(********************************)
(** Decidable equality on lists *)
(********************************)


Lemma list_eq_dec : ((x,y:A){x=y}+{~x=y})->(x,y:list){x=y}+{~x=y}.
Proof.
  NewInduction x as [|a l IHl]; NewDestruct y as [|a0 l0]; Auto.
  NewDestruct (H a a0) as [e|e].
  NewDestruct (IHl l0) as [e'|e'].
  Left; Rewrite e; Rewrite e'; Trivial.
  Right; Red; Intro.
  Apply e'; Injection H0; Trivial.
  Right; Red; Intro.
  Apply e; Injection H0; Trivial.
Qed.

(*************************)
(**  Reverse             *)
(*************************)

Fixpoint rev [l:list] : list :=
   Cases l of
      nil        => nil
   | (cons x l') => (rev l')^(cons x nil)
   end.

Lemma distr_rev : 
 (x,y:list) (rev (x^y))=((rev y)^(rev x)).
Proof.
 NewInduction x as [|a l IHl].
 NewDestruct y.
 Simpl.
 Auto.

 Simpl.
 Apply app_nil_end;Auto.

 Intro y.
 Simpl.
 Rewrite (IHl y).
 Apply (app_ass (rev y) (rev l) (cons a nil)).
Qed.

Remark  rev_unit : (l:list)(a:A) (rev  l^(cons a nil))= (cons a (rev l)).
Proof.
 Intros.
 Apply (distr_rev l (cons a nil));Simpl;Auto.
Qed.

Lemma idempot_rev : (l:list)(rev (rev l))=l.
Proof.
 NewInduction l as [|a l IHl].
 Simpl;Auto.

 Simpl.
 Rewrite (rev_unit (rev l) a).
 Rewrite -> IHl;Auto.
Qed.

(*********************************************)
(**  Reverse Induction Principle on Lists    *)
(*********************************************)

Section Reverse_Induction.

Unset Implicit Arguments.

Remark rev_list_ind: (P:list->Prop)
      (P nil)
       ->((a:A)(l:list)(P (rev l))->(P (rev  (cons a l)))) 
             ->(l:list) (P (rev  l)).
Proof.
 NewInduction l; Auto.
Qed.
Set Implicit Arguments.

Lemma rev_ind : 
 (P:list->Prop)
   (P nil)->
    ((x:A)(l:list)(P l)->(P l^(cons x nil)))
      ->(l:list)(P l).
Proof.
 Intros.
 Generalize (idempot_rev l) .
 Intros E;Rewrite <- E.
 Apply (rev_list_ind P).
 Auto.

 Simpl.
 Intros.
 Apply (H0 a (rev l0)).
 Auto.
Qed.

End Reverse_Induction.

End Lists.

Implicits nil [1].

Hints Resolve nil_cons app_nil_end ass_app app_ass : datatypes v62.
Hints Resolve app_comm_cons  app_cons_not_nil : datatypes v62.
Hints Immediate app_eq_nil : datatypes v62.
Hints Resolve app_eq_unit app_inj_tail : datatypes v62. 
Hints Resolve lel_refl lel_cons_cons lel_cons lel_nil lel_nil nil_cons 
   : datatypes v62.
Hints Resolve in_eq in_cons in_inv in_nil in_app_or in_or_app : datatypes v62.
Hints Resolve incl_refl incl_tl incl_tran incl_appl incl_appr incl_cons incl_app 
  : datatypes v62.

Section Functions_on_lists.

(****************************************************************)
(** Some generic functions on lists and basic functions of them *)
(****************************************************************)

Section Map.
Variables A,B:Set.
Variable  f:A->B.
Fixpoint map [l:(list A)] : (list B) :=
  Cases l of 
     nil       => nil
  | (cons a t) => (cons (f a) (map t))
  end.
End Map.

Lemma in_map : (A,B:Set)(f:A->B)(l:(list A))(x:A)
  (In x l) -> (In (f x) (map f l)).
Proof. 
  NewInduction l as [|a l IHl]; Simpl;
  [ Auto
  | NewDestruct 1;
    [ Left; Apply f_equal with f:=f; Assumption
    | Auto]
  ].
Qed.

Fixpoint flat_map [A,B:Set; f:A->(list B); l:(list A)] : (list B) :=
  Cases l of
    nil => nil
  | (cons x t) => (app (f x) (flat_map f t))
  end.

Fixpoint list_prod [A:Set; B:Set; l:(list A)] : (list B)->(list A*B) :=
  [l']Cases l of
    nil => nil
  | (cons x t) => (app (map [y:B](x,y) l')
      	       	       	     (list_prod t l'))
  end.

Lemma in_prod_aux :
  (A:Set)(B:Set)(x:A)(y:B)(l:(list B))
    (In y l) -> (In (x,y) (map [y0:B](x,y0) l)).
Proof. 
  NewInduction l;
  [ Simpl; Auto
  | Simpl; NewDestruct 1 as [H1|];
    [ Left; Rewrite H1; Trivial
    | Right; Auto]
  ].
Qed.

Lemma in_prod : (A:Set)(B:Set)(l:(list A))(l':(list B))
  (x:A)(y:B)(In x l)->(In y l')->(In (x,y) (list_prod l l')).
Proof. 
  NewInduction l;
  [ Simpl; Tauto
  | Simpl; Intros; Apply in_or_app; NewDestruct H;
    [ Left; Rewrite H; Apply in_prod_aux; Assumption
    | Right; Auto]
  ].
Qed.

(** [(list_power x y)] is [y^x], or the set of sequences of elts of [y]
    indexed by elts of [x], sorted in lexicographic order. *)

Fixpoint list_power [A,B:Set; l:(list A)] : (list B)->(list (list A*B)) :=
  [l']Cases l of
    nil => (cons nil nil)
  | (cons x t) => (flat_map [f:(list A*B)](map [y:B](cons (x,y) f) l') 
      	       	       	    (list_power t l'))
  end.

(************************************)
(** Left-to-right iterator on lists *)
(************************************)

Section Fold_Left_Recursor.
Variables A,B:Set.
Variable  f:A->B->A.
Fixpoint fold_left[l:(list B)] : A -> A :=
[a0]Cases l of
     nil       => a0
  | (cons b t) => (fold_left t (f a0 b))
  end.
End Fold_Left_Recursor.

(************************************)
(** Right-to-left iterator on lists *)
(************************************)

Section Fold_Right_Recursor.
Variables A,B:Set.
Variable  f:B->A->A.
Variable  a0:A.
Fixpoint fold_right [l:(list B)] : A :=
  Cases l of
    nil => a0
  | (cons b t) => (f b (fold_right t))
  end.
End Fold_Right_Recursor.

Theorem fold_symmetric :
  (A:Set)(f:A->A->A)
   ((x,y,z:A)(f x (f y z))=(f (f x y) z))
    ->((x,y:A)(f x y)=(f y x))
     ->(a0:A)(l:(list A))(fold_left f l a0)=(fold_right f a0 l).
Proof.
NewDestruct l as [|a l].
Reflexivity.
Simpl.
Rewrite <- H0.
Generalize a0 a.
NewInduction l as [|a3 l IHl]; Simpl.
Trivial.
Intros.
Rewrite H.
Rewrite (H0 a2).
Rewrite <- (H a1).
Rewrite (H0 a1).
Rewrite IHl.
Reflexivity.
Qed.

End Functions_on_lists.

V7only [Implicits nil [].].

(** Exporting list notations *)

V8Infix "::" cons (at level 60, right associativity) : list_scope.

Infix RIGHTA 7 "^" app : list_scope V8only RIGHTA 60 "++".

Open Scope list_scope.

Delimits Scope list_scope with list.

Bind Scope list_scope with list.
