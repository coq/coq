(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*************)
(* Booleans  *)
(* The type [bool] is defined in the prelude as \\
    [Inductive bool : Set := true : bool | false : bool] *)

(* Interpretation of booleans as Proposition *)
Definition Is_true := [b:bool](Cases b of
                                 true  => True
                               | false => False
                               end).
Hints Unfold Is_true : bool.

Lemma Is_true_eq_left : (x:bool)x=true -> (Is_true x).
Proof.
  Intros; Rewrite H; Auto with bool.
Save.

Lemma Is_true_eq_right : (x:bool)true=x -> (Is_true x).
Proof.
  Intros; Rewrite <- H; Auto with bool.
Save.

Hints Immediate Is_true_eq_right Is_true_eq_left : bool.

(*******************)
(*s Discrimination *)
(*******************)

Lemma diff_true_false : ~true=false.
Goal.
Unfold not; Intro contr; Change (Is_true false).
Elim contr; Simpl; Trivial with bool.
Save.
Hints Resolve diff_true_false : bool v62.

Lemma diff_false_true : ~false=true.
Goal.
Red; Intros H; Apply diff_true_false.
Symmetry.
Assumption.
Save.
Hints Resolve diff_false_true : bool v62.

Lemma eq_true_false_abs : (b:bool)(b=true)->(b=false)->False.
Intros b H; Rewrite H; Auto with bool.
Save.
Hints Resolve eq_true_false_abs : bool.

Lemma not_true_is_false : (b:bool)~b=true->b=false.
Destruct b.
Intros.
Red in H; Elim H.
Reflexivity.
Intros abs.
Reflexivity.
Save.

Lemma not_false_is_true : (b:bool)~b=false->b=true.
Destruct b.
Intros.
Reflexivity.
Intro H; Red in H; Elim H.
Reflexivity.
Save.

(**********************)
(*s Order on booleans *)
(**********************)

Definition leb := [b1,b2:bool]
  Cases b1 of 
  | true => b2=true
  | false => True 
  end.
Hints Unfold leb : bool v62.

(*************)
(*s Equality *)
(*************)

Definition eqb : bool->bool->bool :=
 [b1,b2:bool]
    Cases b1 b2 of
      true  true  => true
    | true  false => false
    | false true  => false
    | false false => true
    end.

Lemma eqb_refl : (x:bool)(Is_true (eqb x x)).
Destruct x; Simpl; Auto with bool.
Save.

Lemma eqb_eq : (x,y:bool)(Is_true (eqb x y))->x=y.
Destruct x; Destruct y; Simpl; Tauto.
Save.

Lemma Is_true_eq_true : (x:bool) (Is_true x) -> x=true.
Destruct x; Simpl; Tauto.
Save.
 
Lemma Is_true_eq_true2 : (x:bool)  x=true -> (Is_true x).
Destruct x; Simpl; Auto with bool.
Save.

Lemma eqb_subst : 
  (P:bool->Prop)(b1,b2:bool)(eqb b1 b2)=true->(P b1)->(P b2).
Unfold eqb .
Intros P b1.
Intros b2.
Case b1.
Case b2.
Trivial with bool.
Intros H.
Inversion_clear H.
Case b2.
Intros H.
Inversion_clear H.
Trivial with bool.
Save.

Lemma eqb_reflx : (b:bool)(eqb b b)=true.
Intro b.
Case b.
Trivial with bool.
Trivial with bool.
Save.

Lemma eqb_prop : (a,b:bool)(eqb a b)=true -> a=b.
Destruct a; Destruct b; Simpl; Intro;
  Discriminate H Orelse Reflexivity.
Save.


(************************)
(*s Logical combinators *)
(************************)
 
Definition ifb : bool -> bool -> bool -> bool
     := [b1,b2,b3:bool](Cases b1 of true => b2 | false => b3 end).

Definition andb : bool -> bool -> bool
     := [b1,b2:bool](ifb b1 b2 false).

Definition orb : bool -> bool -> bool
     := [b1,b2:bool](ifb b1 true b2).

Definition implb : bool -> bool -> bool
     := [b1,b2:bool](ifb b1 b2 true).

Definition xorb :  bool -> bool -> bool
     := [b1,b2:bool]
    Cases b1 b2 of
      true  true  => false
    | true  false => true
    | false true  => true
    | false false => false
    end.

Definition negb := [b:bool]Cases b of
                             true  => false
                           | false => true
                           end.


(**************************)
(*s Lemmas about [negb]   *)
(**************************)

Lemma negb_intro : (b:bool)b=(negb (negb b)).
Goal.
Induction b; Reflexivity.
Save.

Lemma negb_elim : (b:bool)(negb (negb b))=b.
Goal.
Induction b; Reflexivity.
Save.
       
Lemma negb_orb : (b1,b2:bool)
  (negb (orb b1 b2)) = (andb (negb b1) (negb b2)).
Proof.
  Destruct b1; Destruct b2; Simpl; Reflexivity.
Qed.

Lemma negb_andb : (b1,b2:bool)
  (negb (andb b1 b2)) = (orb (negb b1) (negb b2)).
Proof.
  Destruct b1; Destruct b2; Simpl; Reflexivity.
Qed.

Lemma negb_sym : (b,b':bool)(b'=(negb b))->(b=(negb b')).
Goal.
Induction b; Induction b'; Intros; Simpl; Trivial with bool.
Save.

Lemma no_fixpoint_negb : (b:bool)~(negb b)=b.
Goal.
Induction b; Simpl; Unfold not; Intro; Apply diff_true_false; Auto with bool.
Save.

Lemma eqb_negb1 : (b:bool)(eqb (negb b) b)=false.
Destruct b.
Trivial with bool.
Trivial with bool.
Save.
 
Lemma eqb_negb2 : (b:bool)(eqb b (negb b))=false.
Destruct b.
Trivial with bool.
Trivial with bool.
Save.


Lemma if_negb : (A:Set) (b:bool) (x,y:A) (if (negb b) then x else y)=(if b then y else x).
Proof.
  Induction b;Trivial.
Qed.


(****************************)
(*s A few lemmas about [or] *)
(****************************)

Lemma orb_prop : 
  (a,b:bool)(orb a b)=true -> (a = true)\/(b = true).
Induction a; Induction b; Simpl; Try (Intro H;Discriminate H); Auto with bool.
Save.

Lemma orb_prop2 : 
  (a,b:bool)(Is_true (orb a b)) -> (Is_true a)\/(Is_true b).
Induction a; Induction b; Simpl; Try (Intro H;Discriminate H); Auto with bool.
Save.

Lemma orb_true_intro 
    : (b1,b2:bool)(b1=true)\/(b2=true)->(orb b1 b2)=true.
Destruct b1; Auto with bool.
Destruct 1; Intros.
Elim diff_true_false; Auto with bool.
Rewrite H0; Trivial with bool.
Save.
Hints Resolve orb_true_intro : bool v62.

Lemma orb_b_true : (b:bool)(orb b true)=true.
Auto with bool.
Save.
Hints Resolve orb_b_true : bool v62.

Lemma orb_true_b : (b:bool)(orb true b)=true.
Trivial with bool.
Save.

Lemma orb_true_elim : (b1,b2:bool)(orb b1 b2)=true -> {b1=true}+{b2=true}.
Destruct b1; [Auto with bool | Destruct b2; Auto with bool].
Save.
Lemma orb_false_intro 
    : (b1,b2:bool)(b1=false)->(b2=false)->(orb b1 b2)=false.
Intros b1 b2 H1 H2; Rewrite H1; Rewrite H2; Trivial with bool.
Save.
Hints Resolve orb_false_intro : bool v62.

Lemma orb_b_false : (b:bool)(orb b false)=b.
Proof.
  Destruct b; Trivial with bool.
Save.
Hints Resolve orb_b_false : bool v62.

Lemma orb_false_b : (b:bool)(orb false b)=b.
Proof.
  Destruct b; Trivial with bool.
Save.
Hints Resolve orb_false_b : bool v62.

Lemma orb_false_elim : 
    (b1,b2:bool)(orb b1 b2)=false -> (b1=false)/\(b2=false).
Proof.
  Destruct b1.
  Intros; Elim diff_true_false; Auto with bool.
  Destruct b2.
  Intros; Elim diff_true_false; Auto with bool.
  Auto with bool.
Save.

Lemma orb_neg_b :
  (b:bool)(orb b (negb b))=true.
Proof.
  Destruct b; Reflexivity.
Save.
Hints Resolve orb_neg_b : bool v62.

Lemma orb_sym : (b1,b2:bool)(orb b1 b2)=(orb b2 b1).
Destruct b1; Destruct b2; Reflexivity.
Save.

Lemma orb_assoc : (b1,b2,b3:bool)(orb b1 (orb b2 b3))=(orb (orb b1 b2) b3).
Proof.
  Destruct b1; Destruct b2; Destruct b3; Reflexivity.
Save.

Hints Resolve orb_sym orb_assoc orb_b_false orb_false_b : bool v62.

(*****************************)
(*s A few lemmas about [and] *)
(*****************************)

Lemma andb_prop : 
  (a,b:bool)(andb a b) = true -> (a = true)/\(b = true).

Proof.
  Induction a; Induction b; Simpl; Try (Intro H;Discriminate H);
  Auto with bool.
Save.
Hints Resolve andb_prop : bool v62.

Lemma andb_prop2 : 
  (a,b:bool)(Is_true (andb a b)) -> (Is_true a)/\(Is_true b).
Proof.
  Induction a; Induction b; Simpl; Try (Intro H;Discriminate H);
  Auto with bool.
Save.
Hints Resolve andb_prop2 : bool v62.

Lemma andb_true_intro : (b1,b2:bool)(b1=true)/\(b2=true)->(andb b1 b2)=true.
Proof.
  Destruct b1; Destruct b2; Simpl; Tauto Orelse Auto with bool.
Save.
Hints Resolve andb_true_intro : bool v62.

Lemma andb_true_intro2 : 
  (b1,b2:bool)(Is_true b1)->(Is_true b2)->(Is_true (andb b1 b2)).
Proof.
  Destruct b1; Destruct b2; Simpl; Tauto.
Save.
Hints Resolve andb_true_intro2 : bool v62.

Lemma andb_false_intro1 
    : (b1,b2:bool)(b1=false)->(andb b1 b2)=false.
Destruct b1; Destruct b2; Simpl; Tauto Orelse Auto with bool.
Save.

Lemma andb_false_intro2 
    : (b1,b2:bool)(b2=false)->(andb b1 b2)=false.
Destruct b1; Destruct b2; Simpl; Tauto Orelse Auto with bool.
Save.

Lemma andb_b_false : (b:bool)(andb b false)=false.
Destruct b; Auto with bool.
Save.

Lemma andb_false_b : (b:bool)(andb false b)=false.
Trivial with bool.
Save.

Lemma andb_b_true : (b:bool)(andb b true)=b.
Destruct b; Auto with bool.
Save.

Lemma andb_true_b : (b:bool)(andb true b)=b.
Trivial with bool.
Save.

Lemma andb_false_elim : 
    (b1,b2:bool)(andb b1 b2)=false -> {b1=false}+{b2=false}.
Destruct b1; Destruct b2; Simpl; Auto with bool.
Save.
Hints Resolve andb_false_elim : bool v62.

Lemma andb_neg_b :
   (b:bool)(andb b (negb b))=false.
Destruct b; Reflexivity.
Save.   
Hints Resolve andb_neg_b : bool v62.

Lemma andb_sym : (b1,b2:bool)(andb b1 b2)=(andb b2 b1).
Destruct b1; Destruct b2; Reflexivity.
Save.

Lemma andb_assoc : (b1,b2,b3:bool)(andb b1 (andb b2 b3))=(andb (andb b1 b2) b3).
Destruct b1; Destruct b2; Destruct b3; Reflexivity.
Save.

Hints Resolve andb_sym andb_assoc : bool v62.

(*******************************)
(*s Properties of [xorb]       *)
(*******************************)

Lemma xorb_false : (b:bool) (xorb b false)=b.
Proof.
  Induction b; Trivial.
Qed.

Lemma false_xorb : (b:bool) (xorb false b)=b.
Proof.
  Induction b; Trivial.
Qed.

Lemma xorb_true : (b:bool) (xorb b true)=(negb b).
Proof.
  Trivial.
Qed.

Lemma true_xorb : (b:bool) (xorb true b)=(negb b).
Proof.
  Induction b; Trivial.
Qed.

Lemma xorb_nilpotent : (b:bool) (xorb b b)=false.
Proof.
  Induction b; Trivial.
Qed.

Lemma xorb_comm : (b,b':bool) (xorb b b')=(xorb b' b).
Proof.
  Induction b; Induction b'; Trivial.
Qed.

Lemma xorb_assoc : (b,b',b'':bool) (xorb (xorb b b') b'')=(xorb b (xorb b' b'')).
Proof.
  Induction b; Induction b'; Induction b''; Trivial.
Qed.

Lemma xorb_eq : (b,b':bool) (xorb b b')=false -> b=b'.
Proof.
  Induction b; Induction b'; Trivial.
  Unfold xorb. Intros. Rewrite H. Reflexivity.
Qed.

Lemma xorb_move_l_r_1 : (b,b',b'':bool) (xorb b b')=b'' -> b'=(xorb b b'').
Proof.
  Intros. Rewrite <- (false_xorb b'). Rewrite <- (xorb_nilpotent b). Rewrite xorb_assoc.
  Rewrite H. Reflexivity.
Qed.

Lemma xorb_move_l_r_2 : (b,b',b'':bool) (xorb b b')=b'' -> b=(xorb b'' b').
Proof.
  Intros. Rewrite (xorb_comm b b') in H. Rewrite (xorb_move_l_r_1 b' b b'' H). Apply xorb_comm.
Qed.

Lemma xorb_move_r_l_1 : (b,b',b'':bool) b=(xorb b' b'') -> (xorb b' b)=b''.
Proof.
  Intros. Rewrite H. Rewrite <- xorb_assoc. Rewrite xorb_nilpotent. Apply false_xorb.
Qed.

Lemma xorb_move_r_l_2 : (b,b',b'':bool) b=(xorb b' b'') -> (xorb b b'')=b'.
Proof.
  Intros. Rewrite H. Rewrite xorb_assoc. Rewrite xorb_nilpotent. Apply xorb_false.
Qed.

(*******************************)
(*s De Morgan's law            *)
(*******************************)

Lemma demorgan1 : (b1,b2,b3:bool)
  (andb b1 (orb b2 b3)) = (orb (andb b1 b2) (andb b1 b3)).
Destruct b1; Destruct b2; Destruct b3; Reflexivity.
Save.

Lemma demorgan2 : (b1,b2,b3:bool)
  (andb (orb b1 b2) b3) = (orb (andb b1 b3) (andb b2 b3)).
Destruct b1; Destruct b2; Destruct b3; Reflexivity.
Save.

Lemma demorgan3 : (b1,b2,b3:bool)
  (orb b1 (andb b2 b3)) = (andb (orb b1 b2) (orb b1 b3)).
Destruct b1; Destruct b2; Destruct b3; Reflexivity.
Save.

Lemma demorgan4 : (b1,b2,b3:bool)
  (orb (andb b1 b2) b3) = (andb (orb b1 b3) (orb b2 b3)).
Destruct b1; Destruct b2; Destruct b3; Reflexivity.
Save.

Lemma absoption_andb : (b1,b2:bool)
  (andb b1 (orb b1 b2)) = b1.
Proof.
  Destruct b1; Destruct b2; Simpl; Reflexivity.
Qed.

Lemma absoption_orb : (b1,b2:bool)
  (orb b1 (andb b1 b2)) = b1.
Proof.
  Destruct b1; Destruct b2; Simpl; Reflexivity.
Qed.
