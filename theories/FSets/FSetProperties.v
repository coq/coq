(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(** This module proves many properties of finite sets that 
    are consequences of the axiomatization in [FSetInterface] *) 

Require Omega.

Import nat_scope.
Open Scope nat_scope.

Require Export FSetInterface. 
Require Export Bool.
Require Export Sumbool.
Require Export Zerob. 
Set Implicit Arguments.

(* For proving (Setoid_Theory ? (eq ?)) *)
Tactic Definition ST :=
  Constructor; Intros;[ Trivial | Symmetry; Trivial | EApply trans_eq; EAuto ].
Hint st : core := Extern 1 (Setoid_Theory ? (eq ?)) ST.

Definition gen_st : (A:Set)(Setoid_Theory ? (eq A)).
Auto.
Qed.


Module Properties [M:S].
  Import M.
  Import Logic. (* for unmasking eq. *)  
  Import Peano. (* for unmasking lt *)
  
  Module ME := MoreOrderedType E.  

  Section Old_Spec_Now_Properties. 

  Variable s,s' : t.
  Variable x,y,z : elt.

  Lemma mem_eq: 
    (E.eq x y) -> (mem x s)=(mem y s).
  Proof. 
  Intros; Apply bool_1.
  Generalize (!mem_1 s x) (!mem_1 s y) (!mem_2 s x) (!mem_2 s y).
  Intuition. 
  EAuto.
  Apply H0; Apply In_1 with y; Auto.
  Qed.

  Lemma equal_mem_1: 
    ((a:elt)(mem a s)=(mem a s')) -> (equal s s')=true.
  Proof. 
  Intros; Apply equal_1; Unfold Equal; Intuition; EAuto.
  Qed.

  Lemma equal_mem_2: 
    (equal s s')=true -> (a:elt)(mem a s)=(mem a s').
  Proof. 
  Intros; Apply bool_1.
  Intros; Cut (Equal s s'); [Clear H; Unfold Equal|Auto].
  Intros H; Generalize (H a); Intuition.
  Qed.

  Lemma subset_mem_1: 
    ((a:elt)(mem a s)=true->(mem a s')=true) -> (subset s s')=true.
  Proof. 
  Intros; Apply subset_1; Unfold Subset; Intuition; EAuto.
  Qed.

  Lemma subset_mem_2: 
    (subset s s')=true -> (a:elt)(mem a s)=true -> (mem a s')=true.
  Proof. 
  Intros; Apply bool_1.
  Cut (Subset s s'); [Clear H; Unfold Subset|Auto].
  Intros H; Generalize (H a); Intuition.
  Qed.
  
  Lemma empty_mem: (mem x empty)=false.
  Proof. 
  Apply not_true_is_false; Intro; Absurd (In x empty); Auto.
  Qed.

  Lemma is_empty_equal_empty: (is_empty s)=(equal s empty).
  Proof. 
  Generalize empty_1 (!is_empty_1 s) (!is_empty_2 s) 
            (!equal_1 s empty) (!equal_2 s empty).
  Unfold Empty Equal.
  Case (is_empty s); Case (equal s empty); Intuition.
  Clear H3 H1.
  Symmetry; Apply H2; Intuition.
  Generalize (H4 a); Intuition.
  Generalize (H a); Intuition.
  Clear H1 H3.
  Apply H0; Intuition.
  Generalize (H4 a); Intuition.
  Generalize (H a); Intuition.
  Qed.
  
  Lemma choose_mem_1: (choose s)=(Some ? x) -> (mem x s)=true.
  Proof.  
  Auto.
  Qed.

  Lemma choose_mem_2: (choose s)=(None ?) -> (is_empty s)=true.
  Proof.
  Auto.
  Qed.

  Lemma add_mem_1: (mem x (add x s))=true.
  Proof.
  Auto.
  Qed.  
 
  Lemma add_mem_2: 
  ~ (E.eq x y) -> (mem y (add x s))=(mem y s).
  Proof. 
  Intros; Apply bool_1; Intuition; EAuto.
  Qed.

  Lemma remove_mem_1: (mem x (remove x s))=false.
  Proof. 
  Apply not_true_is_false; Intro; Absurd (In x (remove x s)); Auto.
  Qed. 
 
  Lemma remove_mem_2: 
  ~ (E.eq x y) -> (mem y (remove x s))=(mem y s).
  Proof. 
  Intros; Apply bool_1; Intuition; EAuto. 
  Qed.

  Lemma singleton_equal_add: 
    (equal (singleton x) (add x empty))=true.
  Proof.
  Apply equal_1; Unfold Equal; Intuition.
  Apply In_1 with x; Auto.
  Assert (E.eq a x); Auto.
  Elim (ME.eq_dec a x); Auto.
  Intros; Assert (In a empty). 
  EApply add_3; EAuto.  
  Generalize (empty_1 H0); Intuition.
  Qed.  

  Lemma union_mem: 
    (mem x (union s s'))=(orb (mem x s) (mem x s')).
  Proof. 
  Apply bool_1; Intuition.
  Elim (!union_1 s s' x); Intuition.
  Elim (orb_prop ? ? H); Intuition.
  Qed.

  Lemma inter_mem: 
    (mem x (inter s s'))=(andb (mem x s) (mem x s')).
  Proof. 
  Apply bool_1; Intuition.
  Apply andb_true_intro; Intuition EAuto.
  Elim (andb_prop ?? H); Intuition.
  Qed.

  Lemma diff_mem: 
    (mem x (diff s s'))=(andb (mem x s) (negb (mem x s'))).
  Proof. 
  Generalize (!diff_1 s s' x) (!diff_2 s s' x) (!diff_3 s s' x).
  LetTac s0 := (diff s s').
  Generalize (!mem_1 s x) (!mem_1 s' x) (!mem_1 s0 x) 
             (!mem_2 s x) (!mem_2 s' x) (!mem_2 s0 x).
  Case (mem x s); Case (mem x s'); Case (mem x s0); Intuition.
  Qed.

  Section Cardinal.
  
  Lemma Add_add : 
    (s:t)(x:elt)(Add x s (add x s)).
  Proof.
    Unfold Add; Intros; Intuition.
    Elim (ME.eq_dec x0 y0); Intros; Auto.
    Right.
    EApply add_3; EAuto.
    Apply In_1 with x0; Auto. 
  Qed.

  Lemma Add_remove : (s:t)(x:elt)(In x s) -> (Add x (remove x s) s). 
  Proof. 
    Intros; Unfold Add; Intuition.
    Elim (ME.eq_dec x0 y0); Intros; Auto.
    Apply In_1 with x0; Auto.
    EAuto.
  Qed.
 
  Hints Resolve Add_add Add_remove. 

  Lemma Equal_remove : (s,s':t)(x:elt)(In x s)->(Equal s s')-> 
     (Equal (remove x s) (remove x s')).
  Proof.
     Unfold Equal; Intros.
     Elim (ME.eq_dec x0 a); Intros; Auto. 
     Split; Intros.
     Absurd (In x0 (remove x0 s0)); Auto; Apply In_1 with a; Auto.
     Absurd (In x0 (remove x0 s'0)); Auto; Apply In_1 with a; Auto. 
     Elim (H0 a); Intros. 
     Split; Intros; Apply remove_2; Auto; 
      [Apply H1|Apply H2]; EApply remove_3;EAuto.    
  Save.

  Hints Resolve Equal_remove.

  Lemma cardinal_inv_1 : (s:t)(cardinal s)=O -> (Empty s). 
  Proof. 
    Intros; Generalize (!choose_1 s0) (!choose_2 s0).
    Elim (choose s0); Intuition.
    Clear H1; Assert (In a s0); Auto.
    Rewrite (!cardinal_2 (remove a s0) s0 a) in H; Auto.
    Inversion H.
  Save.
  Hints Resolve cardinal_inv_1.
 
  Lemma cardinal_inv_2 : 
     (s:t)(n:nat)(cardinal s)=(S n) -> (EX x:elt | (In x s)).
  Proof. 
    Intros; Generalize (!choose_1 s0) (!choose_2 s0).
    Elim (choose s0); Intuition. 
    Exists a; Auto.
    Intros; Rewrite cardinal_1 in H; Auto; Inversion H.
  Qed.

  Lemma Equal_cardinal_aux : (n:nat)(s,s':t)(cardinal s)=n -> 
       (Equal s s')->(cardinal s)=(cardinal s').
  Proof.
     Induction n.
     Intros.  
     Rewrite H.
     Symmetry.
     Apply cardinal_1.
     Generalize (cardinal_inv_1 H) H0.
     Unfold Empty Equal; Intuition.
     Generalize (H1 a) (H2 a); Intuition.
     Intros.
     Elim (cardinal_inv_2 H0); Intros.
     Assert (In x0 s'0). 
       Generalize (H1 x0); Intuition.  
     Generalize H0.
     Rewrite (!cardinal_2 (remove x0 s0) s0 x0);Auto.
     Rewrite (!cardinal_2 (remove x0 s'0) s'0 x0); Auto.
  Qed.

  Lemma Equal_cardinal : (s,s':t)(Equal s s')->(cardinal s)=(cardinal s').
  Proof. 
    Intros; EApply Equal_cardinal_aux; EAuto.
  Qed.

  End Cardinal.

  Hints Resolve Add_add Add_remove Equal_remove 
                cardinal_inv_1 Equal_cardinal.

  Lemma cardinal_induction : (P : t -> Prop)
     ((s:t)(Empty s)->(P s)) -> 
     ((s,s':t)(P s) -> (x:elt)~(In x s) -> (Add x s s') -> (P s')) -> 
     (n:nat)(s:t)(cardinal s)=n -> (P s).
  Proof.
  Induction n.
  Intros; Apply H; Auto.
  Intros; Elim (cardinal_inv_2 H2); Intros. 
  Apply H0 with (remove x0 s0) x0; Auto.
  Apply H1; Auto.
  Assert (S (cardinal (remove x0 s0))) = (S n0); Auto. 
  Rewrite <- H2; Symmetry.
  EApply cardinal_2; EAuto.
  Qed.

  Lemma set_induction : (P : t -> Prop)
     ((s:t)(Empty s)->(P s)) -> 
     ((s,s':t)(P s) -> (x:elt)~(In x s) -> (Add x s s') -> (P s')) -> 
     (s:t)(P s).
  Proof.
  Intros; EApply cardinal_induction; EAuto.
  Qed.  

  Section Fold. 

  Variable A:Set. 
  Variable eqA:A->A->Prop.
  Variable st:(Setoid_Theory ? eqA).
  Variable i:A.
  Variable f:elt->A->A.
  Variable Comp:(compat_op E.eq eqA f). 
  Variable Assoc:(transpose eqA f).
 
  Lemma fold_empty: (eqA (fold f empty i) i).
  Proof. 
  Apply fold_1; Auto.
  Qed.

  Lemma fold_equal: 
    (equal s s')=true -> (eqA (fold f s i) (fold f s' i)).
  Proof. 
     Pattern s; Apply set_induction; Intros.
     Apply (Seq_trans ?? st) with i; Auto.
     Apply fold_1; Auto.
     Apply Seq_sym; Auto; Apply fold_1; Auto.
     Apply cardinal_inv_1; Rewrite <- (Equal_cardinal (equal_2 H0)); Auto.
     Apply (Seq_trans ?? st) with (f x0 (fold f s0 i)); Auto.
     Apply fold_2 with eqA:=eqA; Auto.
     Apply Seq_sym; Auto; Apply fold_2 with eqA := eqA; Auto.
     Generalize (equal_2 H2) H1; Unfold Add Equal; Intros; 
       Elim (H4 y0); Elim (H3 y0); Intuition.
  Qed.
   
  Lemma fold_add: 
    (mem x s)=false -> (eqA (fold f (add x s) i) (f x (fold f s i))).
  Proof. 
    Intros; Apply fold_2 with eqA:=eqA; Auto.
    Intro; Rewrite mem_1 in H; Auto; Discriminate H. 
  Qed.

  End Fold.

  Lemma cardinal_fold: (cardinal s)=(fold [_]S s O).
  Proof. 
    Pattern s; Apply set_induction; Intros.
    Rewrite cardinal_1; Auto; Symmetry; Apply fold_1;Auto.
    Rewrite (!cardinal_2 s0 s'0 x0);Auto.
    Rewrite H; Symmetry; Change S with ([_]S x0). 
    Apply fold_2 with eqA:=(eq nat); Auto.
  Qed.

  Section Filter.
  
  Variable f:elt->bool.
  Variable Comp: (compat_bool E.eq f).

  Lemma filter_mem: (mem x (filter f s))=(andb (mem x s) (f x)).
  Proof. 
  Apply bool_1; Intuition.
  Apply andb_true_intro; Intuition; EAuto.
  Elim (andb_prop ?? H); Intuition. 
  Qed.

  Lemma for_all_filter: 
    (for_all f s)=(is_empty (filter [x](negb (f x)) s)).
  Proof. 
  Assert Comp' : (compat_bool E.eq [x](negb (f x))). 
    Generalize Comp; Unfold compat_bool; Intros; Apply (f_equal ?? negb); Auto. 
  Apply bool_1; Intuition. 
  Apply is_empty_1.
  Unfold Empty; Intros. 
  Intro.
  Assert (In a s); EAuto.
  Generalize (filter_2 Comp' H0).
  Generalize (for_all_2 Comp H H1); Auto.
  Intros Eq; Rewrite Eq; Intuition.
  Apply for_all_1; Unfold For_all; Intros; Auto. 
  Apply bool_3.
  Red; Intros.
  Elim (is_empty_2 H 3!x0); Auto.
  Qed.

  Lemma exists_filter: 
    (exists f s)=(negb (is_empty (filter f s))).
  Proof. 
  Apply bool_1; Intuition. 
  Elim (exists_2 Comp H); Intuition.
  Apply bool_6.
  Red; Intros; Apply (is_empty_2 H0 3!x0); Auto.
  Generalize (!choose_1 (filter f s)) (!choose_2 (filter f s)).
  Case (choose (filter f s)).
  Intros. 
  Clear H1. 
  Apply exists_1; Auto.
  Exists e; Generalize (H0 e); Intuition; EAuto.
  Intros. 
  Clear H0.
  Rewrite (!is_empty_1 (filter f s)) in H; Auto.
  Discriminate H.
  Qed.

  Lemma partition_filter_1: 
    (equal (fst ? ? (partition f s)) (filter f s))=true.
  Proof. 
  Auto.
  Qed.

  Lemma partition_filter_2: 
    (equal (snd ? ? (partition f s)) (filter [x](negb (f x)) s))=true.
  Proof. 
  Auto.
  Qed.

  End Filter.
  End Old_Spec_Now_Properties.

  Hints Immediate 
  empty_mem   
  is_empty_equal_empty 
  add_mem_1
  remove_mem_1
  singleton_equal_add
  union_mem
  inter_mem
  diff_mem 
  cardinal_fold 
  filter_mem
  for_all_filter
  exists_filter : set. 

  Hints Resolve 
  equal_mem_1
  subset_mem_1
  choose_mem_1
  choose_mem_2
  add_mem_2
  remove_mem_2 : set.

Section MoreProperties.

(*s Properties of [equal] *) 

Lemma equal_refl: (s:t)(equal s s)=true.
Proof.
Auto with set.
Qed.

Lemma equal_sym: (s,s':t)(equal s s')=(equal s' s).
Proof.
Intros.
Apply bool_eq_ind;Intros.
Rewrite equal_mem_1;Auto.
Symmetry;Apply equal_mem_2;Auto.
Apply (bool_eq_ind (equal s s'));Intros;Auto.
Rewrite equal_mem_1 in H;Auto.
Symmetry;Apply equal_mem_2;Auto.
Qed.

Lemma equal_trans: 
 (s,u,v:t)(equal s u)=true -> (equal u v)=true -> (equal s v)=true.
Proof.
Intros.
Apply equal_mem_1;Intros.
Rewrite (equal_mem_2 H).
Apply equal_mem_2;Assumption.
Qed.

Lemma equal_equal: 
 (s,t_,u:t)(equal s t_)=true -> (equal s u)=(equal t_ u).
Proof.
Intros.
Apply bool_eq_ind;Intros.
Apply equal_trans with t_;Auto with set.
Symmetry; Apply bool_eq_ind;Intros;Auto.
Rewrite <- H0.
Apply equal_trans with s;Auto with set.
Rewrite equal_sym;Auto.
Qed.

Lemma equal_cardinal: 
 (s,s':t)(equal s s')=true -> (cardinal s)=(cardinal s').
Proof.
Intros; Apply Equal_cardinal; Auto.
Qed.

Hints Resolve equal_refl equal_cardinal equal_equal:set.
Hints Immediate equal_sym :set.

(* Properties of [subset] *)

Lemma subset_refl: (s:t)(subset s s)=true. 
Proof.
Auto with set.
Qed.

Lemma subset_antisym: 
 (s,s':t)(subset s s')=true -> (subset s' s)=true -> (equal s s')=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Apply bool_eq_ind;Intros.
EApply subset_mem_2;EAuto.
Apply (bool_eq_ind (mem a s));Intros;Auto.
Rewrite <- (subset_mem_2 H H2);Assumption.
Qed.

Lemma subset_trans: 
 (s,t_,u:t)(subset s t_)=true -> (subset t_ u)=true -> (subset s u)=true.
Proof.
Intros.
Apply subset_mem_1;Intros.
Apply subset_mem_2 with t_;Intros;Auto.
Apply subset_mem_2 with s;Auto.
Qed.

Lemma subset_equal: 
 (s,s':t)(equal s s')=true -> (subset s s')=true.
Proof.
Intros.
Apply subset_mem_1;Intros.
Rewrite <- (equal_mem_2 H);Auto.
Qed.

Hints Resolve subset_refl subset_equal subset_antisym :set.

(*s Properties of [empty] *)

Lemma empty_cardinal: (cardinal empty)=O.
Proof.
Rewrite cardinal_fold; Auto with set.
Apply fold_1; Auto.
Qed.

Hints Immediate empty_cardinal :set.

(*s Properties of [choose] *)

Lemma choose_mem_3: 
 (s:t)(is_empty s)=false -> {x:elt|(choose s)=(Some ? x)/\(mem x s)=true}.
Proof.
Intros.
Generalize (!choose_mem_1 s).
Generalize (!choose_mem_2 s).
Case (choose s);Intros.
Exists e;Auto.
LApply H0;Trivial;Intros.
Rewrite H in H2;Discriminate H2.
Qed.

Lemma choose_mem_4: (choose empty)=(None ?).
Proof.
Generalize (!choose_mem_1 empty).
Case (!choose empty);Intros;Auto.
Absurd true=false;Auto with bool.
Rewrite <- (H e);Auto with set.
Qed.

(*s Properties of [add] *)

Lemma add_mem_3: 
 (s:t)(x,y:elt)(mem y s)=true -> (mem y (add x s))=true.
Proof.
Auto.
Qed.

Lemma add_equal: 
 (s:t)(x:elt)(mem x s)=true -> (equal (add x s) s)=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Elim (ME.eq_dec x a); Intros; Auto with set.
Rewrite <- mem_eq with x:=x;Auto.
Rewrite <- (mem_eq s a0);Auto.
Rewrite H;Auto with set.
Qed.

Hints Resolve add_mem_3 add_equal :set.

Lemma add_fold: 
 (A:Set)(eqA:A->A->Prop)(st:(Setoid_Theory ? eqA))
 (f:elt->A->A)(i:A)(compat_op E.eq eqA f) -> (transpose eqA f) ->
 (s:t)(x:elt)(mem x s)=true -> (eqA (fold f (add x s) i) (fold f s i)).
Proof.
Intros; Apply fold_equal with eqA:=eqA; Auto with set.
Qed.

Lemma add_cardinal_1: 
 (s:t)(x:elt)(mem x s)=true -> (cardinal (add x s))=(cardinal s).
Proof.
Auto with set.
Qed.

Lemma add_cardinal_2: 
 (s:t)(x:elt)(mem x s)=false -> (cardinal (add x s))=(S (cardinal s)).
Proof.
Intros.
Do 2 Rewrite cardinal_fold.
Change S with ([_]S x); Apply fold_add with eqA:=(eq nat); Auto.
Qed.

(*s Properties of [remove] *)

Lemma remove_mem_3: 
 (s:t)(x,y:elt)(mem y (remove x s))=true -> (mem y s)=true.
Proof.
Intros s x y;Elim (ME.eq_dec x y); Intro e.
Rewrite <- mem_eq with x:=x;Auto.
Rewrite <- (mem_eq s e);Auto.
Rewrite (remove_mem_1 s x);Intro H;Discriminate H.
Intros;Rewrite <- H;Symmetry;Auto with set.
Qed.

Lemma remove_equal: 
 (s:t)(x:elt)(mem x s)=false -> (equal (remove x s) s)=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Elim (ME.eq_dec x a); Intros;Auto with set.
Rewrite <- mem_eq with x:=x;Auto.
Rewrite <- (mem_eq s a0);Auto;Rewrite H;Auto with set.
Qed.

Hints Resolve remove_mem_3 remove_equal :set.

Lemma add_remove: 
 (s:t)(x:elt)(mem x s)=true -> (equal (add x (remove x s)) s)=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Elim (ME.eq_dec x a); Intros;Auto with set.
Rewrite <- mem_eq with x:=x;Auto.
Rewrite <- (mem_eq s a0);Auto;Rewrite H;Auto with set.
Transitivity (mem a (remove x s));Auto with set.
Qed.

Lemma remove_add: 
 (s:t)(x:elt)(mem x s)=false -> (equal (remove x (add x s)) s)=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Elim (ME.eq_dec x a); Intros;Auto with set.
Rewrite <- mem_eq with x:=x;Auto.
Rewrite <- (mem_eq s a0);Auto;Rewrite H;Auto with set.
Transitivity (mem a (add x s));Auto with set.
Qed.

Hints Immediate add_remove remove_add :set.

Lemma remove_fold_1: 
 (A:Set)(eqA:A->A->Prop)(st:(Setoid_Theory ? eqA))
 (f:elt->A->A)(i:A)(compat_op E.eq eqA f) -> (transpose eqA f) ->
 (s:t)(x:elt)(mem x s)=true -> 
 (eqA (f x (fold f (remove x s) i)) (fold f s i)).
Proof.
Intros.
Apply Seq_sym; Auto.
Apply fold_2 with eqA:=eqA; Auto.
Apply Add_remove; Auto.
Qed.

Lemma remove_fold_2: 
 (A:Set)(eqA:A->A->Prop)(st:(Setoid_Theory ? eqA))
 (f:elt->A->A)(i:A) (compat_op E.eq eqA f) -> (transpose eqA f) ->
 (s:t)(x:elt)(mem x s)=false -> 
 (eqA (fold f (remove x s) i) (fold f s i)).
Proof.
Intros.
Apply fold_equal with eqA:=eqA; Auto with set.
Qed.

Lemma remove_cardinal_1: 
 (s:t)(x:elt)(mem x s)=true -> (S (cardinal (remove x s)))=(cardinal s).
Proof.
Intros.
Do 2 Rewrite cardinal_fold.
Change S with ([_]S x).
Apply remove_fold_1 with eqA:=(eq nat); Auto.
Qed.

Lemma remove_cardinal_2: 
 (s:t)(x:elt)(mem x s)=false -> (cardinal (remove x s))=(cardinal s).
Proof.
Auto with set.
Qed.

(* Properties of [is_empty] *)

Lemma is_empty_cardinal: (s:t)(is_empty s)=(zerob (cardinal s)).
Proof.
Intros.
Apply (bool_eq_ind (is_empty s));Intros.
Rewrite (equal_cardinal 1!s 2!empty).
Rewrite empty_cardinal;Simpl;Trivial.
Rewrite <- H;Symmetry;Auto with set.
Elim (choose_mem_3 H);Intros.
Elim p;Intros.
Rewrite <- (remove_cardinal_1 H1).
Simpl;Trivial.
Qed.

(*s Properties of [singleton] *)

Lemma singleton_mem_1: (x:elt)(mem x (singleton x))=true.
Proof.
Intros.
Rewrite (equal_mem_2 (singleton_equal_add x));Auto with set.
Qed.

Lemma singleton_mem_2: (x,y:elt)~(E.eq x y) -> (mem y (singleton x))=false.
Proof.
Intros.
Rewrite (equal_mem_2 (singleton_equal_add x)).
Rewrite <- (empty_mem y);Auto with set.
Qed.

Lemma singleton_mem_3: (x,y:elt)(mem y (singleton x))=true -> (E.eq x y).
Proof.
Intros.
Elim (ME.eq_dec x y);Intros;Auto.
Qed.

Lemma singleton_cardinal: (x:elt)(cardinal (singleton x))=(S O).
Proof.
Intros.
Rewrite (equal_cardinal (singleton_equal_add x)).
Rewrite add_cardinal_2;Auto with set.
Qed.

(* General recursion principes based on [cardinal] *)

Lemma cardinal_set_rec:  (P:t->Set)
 ((s,s':t)(equal s s')=true -> (P s) -> (P s')) -> 
 ((s:t)(x:elt)(mem x s)=false -> (P s) -> (P (add x s))) -> 
 (P empty) -> (n:nat)(s:t)(cardinal s)=n -> (P s).
Proof.
NewInduction n; Intro s; Generalize (is_empty_cardinal s); 
  Intros eq1 eq2; Rewrite eq2 in eq1; Simpl in eq1.
Rewrite is_empty_equal_empty in eq1.
Rewrite equal_sym in eq1.
Apply (H empty s eq1);Auto.
Elim (choose_mem_3 eq1);Intros;Elim p;Clear p;Intros.
Apply (H (add x (remove x s)) s);Auto with set.
Apply H0;Auto with set.
Apply IHn.
Rewrite <- (remove_cardinal_1 H3) in eq2.
Inversion eq2;Trivial.
Qed.

Lemma set_rec:  (P:t->Set)
 ((s,s':t)(equal s s')=true -> (P s) -> (P s')) ->
 ((s:t)(x:elt)(mem x s)=false -> (P s) -> (P (add x s))) -> 
 (P empty) -> (s:t)(P s).
Proof.
Intros;EApply cardinal_set_rec;EAuto.
Qed.

Lemma cardinal_set_ind:  (P:t->Prop)
 ((s,s':t)(equal s s')=true -> (P s) -> (P s')) -> 
 ((s:t)(x:elt)(mem x s)=false -> (P s) -> (P (add x s))) -> 
 (P empty) -> (n:nat)(s:t)(cardinal s)=n -> (P s).
Proof.
NewInduction n; Intro s; Generalize (is_empty_cardinal s); 
  Intros eq1 eq2; Rewrite eq2 in eq1; Simpl in eq1.
Rewrite is_empty_equal_empty in eq1.
Rewrite equal_sym in eq1.
Apply (H empty s eq1);Auto.
Elim (choose_mem_3 eq1);Intros;Elim p;Clear p;Intros.
Apply (H (add x (remove x s)) s);Auto with set.
Apply H0;Auto with set.
Apply IHn.
Rewrite <- (remove_cardinal_1 H3) in eq2.
Inversion eq2;Trivial.
Qed.

Lemma set_ind:  (P:t->Prop)
 ((s,s':t)(equal s s')=true -> (P s) -> (P s')) ->
 ((s:t)(x:elt)(mem x s)=false -> (P s) -> (P (add x s))) -> 
 (P empty) -> (s:t)(P s).
Proof.
Intros;EApply cardinal_set_ind;EAuto.
Qed.

(*s Properties of [fold] *)

Lemma fold_commutes:
 (A:Set)(eqA:A->A->Prop)(st:(Setoid_Theory ? eqA))
 (f:elt->A->A)(i:A)(compat_op E.eq eqA f) -> (transpose eqA f) -> (s:t)(x:elt)
 (eqA (fold f s (f x i)) (f x (fold f s i))).
Proof.
Intros; Pattern s; Apply set_ind.
Intros.
Apply (Seq_trans ?? st) with (fold f s0 (f x i)).
Apply fold_equal with eqA:=eqA; Auto with set.
Rewrite equal_sym; Auto.
Apply (Seq_trans ?? st) with (f x (fold f s0 i)); Auto.
Apply H; Auto.
Apply fold_equal with eqA:=eqA; Auto.
Intros. 
Apply (Seq_trans ?? st) with (f x0 (fold f s0 (f x i))).
Apply fold_add with eqA:=eqA; Auto.
Apply (Seq_trans ?? st) with (f x0 (f x (fold f s0 i))).
Apply H; Auto.
Apply (Seq_trans ?? st) with (f x (f x0 (fold f s0 i))).
Apply H0; Auto.
Apply H; Auto.
Apply Seq_sym; Auto.
Apply fold_add with eqA:=eqA; Auto.
Apply (Seq_trans ?? st) with (f x i).
Apply fold_empty; Auto.
Apply Seq_sym; Auto.
Apply H; Auto.
Apply fold_empty; Auto.
Qed.

Lemma fold_plus: 
 (s:t)(p:nat)(fold [_]S s p)=(fold [_]S s O)+p.
Proof.
Assert st := (gen_st nat).
Assert fe: (compat_op E.eq (eq ?) [_:elt]S). Unfold compat_op; Auto. 
Assert fp: (transpose (eq ?) [_:elt]S). Unfold transpose;Auto.
Intros s p;Pattern s;Apply set_ind.
Intros; Rewrite <- (fold_equal st p fe fp H).
Rewrite <- (fold_equal st O fe fp H);Assumption.
Intros.
Assert (p:nat)(fold [_]S (add x s0) p) = (S (fold [_]S s0 p)).
Change S with ([_]S x). 
Intros; Apply fold_add with eqA:=(eq nat); Auto.
Rewrite (H1 p).
Rewrite (H1 O).
Rewrite H0.
Simpl; Auto.
Intros; Do 2 Rewrite (fold_empty st);Auto.
Qed.

(*s Properties of [union] *)

Lemma union_sym:
 (s,s':t)(equal (union s s') (union s' s))=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Do 2 Rewrite union_mem;Auto with bool.
Qed.

Lemma union_subset_equal: 
 (s,s':t)(subset s s')=true->(equal (union s s') s')=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Rewrite union_mem.
Apply (bool_eq_ind (mem a s));Intros;Simpl;Auto with set.
Rewrite (subset_mem_2 H H0);Auto.
Qed.

Lemma union_equal_1: 
 (s,s',s'':t)(equal s s')=true->
 (equal (union s s'') (union s' s''))=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Do 2 (Rewrite union_mem;Idtac).
Rewrite (equal_mem_2 H a);Auto.
Qed.

Lemma union_equal_2: 
 (s,s',s'':t)(equal s' s'')=true->
 (equal (union s s') (union s s''))=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Do 2 (Rewrite union_mem;Idtac).
Rewrite (equal_mem_2 H a);Auto.
Qed.

Lemma union_assoc: 
 (s,s',s'':t)
 (equal (union (union s s') s'') (union s (union s' s'')))=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Do 4 Rewrite union_mem.
Rewrite orb_assoc;Auto.
Qed.

Lemma add_union_singleton: 
 (s:t)(x:elt)(equal (add x s) (union (singleton x) s))=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Rewrite union_mem.
Elim (ME.eq_dec x a);Intros.
Rewrite <- (mem_eq (add x s) a0).
Rewrite <- (mem_eq (singleton x) a0).
Rewrite <- (mem_eq s a0).
Rewrite add_mem_1;Rewrite singleton_mem_1;Simpl;Auto.
Rewrite singleton_mem_2;Simpl;Auto with set.
Qed.

Lemma union_add: 
 (s,s':t)(x:elt)
 (equal (union (add x s) s') (add x (union s s')))=true.
Proof.
Intros;Apply equal_trans with (union (union (singleton x) s) s').
Apply union_equal_1;Apply add_union_singleton.
Apply equal_trans with (union (singleton x) (union s s')).
Apply union_assoc.
Rewrite equal_sym;Apply add_union_singleton.
Qed.

(* caracterisation of [union] via [subset] *)

Lemma union_subset_1:
 (s,s':t)(subset s (union s s'))=true.
Proof.
Intros;Apply subset_mem_1;Intros;Rewrite union_mem;Rewrite H;Auto.
Qed.

Lemma union_subset_2:
 (s,s':t)(subset s' (union s s'))=true.
Proof.
Intros;Apply subset_mem_1;Intros;Rewrite union_mem;Rewrite H;Apply orb_b_true.
Qed.

Lemma union_subset_3:
 (s,s',s'':t)(subset s s'')=true -> (subset s' s'')=true -> 
    (subset (union s s') s'')=true.
Proof.
Intros;Apply subset_mem_1;Intros;Rewrite union_mem in H1.
Elim (orb_true_elim ? ? H1);Intros.
Apply (subset_mem_2 H a0).
Apply (subset_mem_2 H0 b).
Qed.

(*s Properties of [inter] *) 

Lemma inter_sym:
 (s,s':t)(equal (inter s s') (inter s' s))=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Do 2 Rewrite inter_mem.
Auto with bool.
Qed.

Lemma inter_subset_equal: 
 (s,s':t)(subset s s')=true->(equal (inter s s') s)=true.
Proof.
Intros.
Apply equal_mem_1;Intros.
Rewrite inter_mem.
Apply (bool_eq_ind (mem a s));Intros;Simpl;Auto.
Rewrite (subset_mem_2 H H0);Auto.
Qed.

Lemma inter_equal_1: 
 (s,s',s'':t)(equal s s')=true->
 (equal (inter s s'') (inter s' s''))=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Do 2 (Rewrite inter_mem;Idtac).
Rewrite (equal_mem_2 H a);Auto.
Qed.

Lemma inter_equal_2: 
 (s,s',s'':t)(equal s' s'')=true->
 (equal (inter s s') (inter s s''))=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Do 2 (Rewrite inter_mem;Idtac).
Rewrite (equal_mem_2 H a);Auto.
Qed.

Lemma inter_assoc: 
 (s,s',s'':t)
 (equal (inter (inter s s') s'') (inter s (inter s' s'')))=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Do 4 Rewrite inter_mem.
Rewrite andb_assoc;Auto.
Qed.

Lemma union_inter_1: 
 (s,s',s'':t)
 (equal (inter (union s s') s'') (union (inter s s'') (inter s' s'')))=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Rewrite union_mem.
Do 3 Rewrite inter_mem.
Rewrite union_mem. 
Apply demorgan2.
Qed.

Lemma union_inter_2: 
 (s,s',s'':t)
 (equal (union (inter s s') s'') (inter (union s s'') (union s' s'')))=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Rewrite union_mem.
Do 2 Rewrite inter_mem.
Do 2 Rewrite union_mem. 
Apply demorgan4.
Qed.

Lemma inter_add_1: 
 (s,s':t)(x:elt)(mem x s')=true -> 
 (equal (inter (add x s) s') (add x (inter s s')))=true.
Proof.
Intros;Apply equal_trans with (inter (union (singleton x) s) s').
Apply inter_equal_1;Apply add_union_singleton.
Apply equal_trans with (union (inter (singleton x) s') (inter s s')).
Apply union_inter_1.
Apply equal_trans with (union (singleton x) (inter s s')).
Apply union_equal_1.
Apply inter_subset_equal.
Apply subset_mem_1;Intros.
Rewrite <- (mem_eq s' (singleton_mem_3 H0));Auto.
Rewrite equal_sym;Apply add_union_singleton.
Qed.

Lemma inter_add_2: 
 (s,s':t)(x:elt)(mem x s')=false -> 
 (equal (inter (add x s) s') (inter s s'))=true.
Proof.
Intros;Apply equal_trans with (inter (union (singleton x) s) s').
Apply inter_equal_1;Apply add_union_singleton.
Apply equal_trans with (union (inter (singleton x) s') (inter s s')).
Apply union_inter_1.
Apply union_subset_equal.
Apply subset_mem_1;Intros.
Rewrite inter_mem in H0.
Elim (andb_prop ? ? H0);Intros.
Absurd (mem a s')=true;Auto.
Rewrite <- (mem_eq s' (singleton_mem_3 H1));Auto.
Rewrite H;Auto with bool.
Qed.

(* caracterisation of [union] via [subset] *)

Lemma inter_subset_1:
 (s,s':t)(subset (inter s s') s)=true.
Proof.
Intros;Apply subset_mem_1;Intros;Rewrite inter_mem in H;Elim (andb_prop ? ? H);Auto.
Qed.

Lemma inter_subset_2:
 (s,s':t)(subset (inter s s') s')=true.
Proof.
Intros;Apply subset_mem_1;Intros;Rewrite inter_mem in H;Elim (andb_prop ? ? H);Auto.
Qed.

Lemma inter_subset_3:
 (s,s',s'':t)(subset s'' s)=true -> (subset s'' s')=true -> 
    (subset s'' (inter s s'))=true.
Intros;Apply subset_mem_1;Intros;Rewrite inter_mem.
Rewrite (subset_mem_2 H H1);Rewrite (subset_mem_2 H0 H1);Auto.
Qed.

(*s Properties of [union],[inter],[fold] and [cardinal] *)

Lemma fold_union_inter: 
 (A:Set)
 (f:elt->A->A)(i:A)(compat_op E.eq (eq ?) f) -> (transpose (eq ?) f) -> 
 (s,s':t)(fold f (union s s') (fold f (inter s s') i))
  = (fold f s (fold f s' i)).
Proof.
Intro A.
LetTac st := (gen_st A).
Intros;Pattern s;Apply set_ind.
Intros; Rewrite <- (fold_equal st i H H0 (inter_equal_1 s' H1)).
Rewrite <- (fold_equal st (fold f s' i) H H0 H1).
Rewrite <- (fold_equal st (fold f (inter s0 s') i)  H H0 (union_equal_1 s' H1));Auto.
Intros.
Rewrite 
 (fold_equal st (fold f (inter (add x s0) s') i) H H0 (union_add s0 s' x)).
Generalize (refl_equal ? (mem x s')); Pattern -1 (mem x s'); Case (mem x s');Intros.
Rewrite (fold_equal st i H H0 (inter_add_1 s0 H3)).
Cut (mem x (inter s0 s'))=false;Intros.
Cut (mem x (union s0 s'))=true;Intros.
Rewrite (fold_add st i H H0 H4).
Rewrite (fold_commutes st);Auto.
Rewrite (fold_equal st (fold f (inter s0 s') i) H H0 (add_equal H5)).
Rewrite (fold_add st (fold f s' i) H H0 H1).
Rewrite H2;Auto.
Rewrite union_mem;Rewrite H3;Apply orb_b_true.
Rewrite inter_mem;Rewrite H1;Simpl;Auto.
Rewrite (fold_equal st i H H0 (inter_add_2 s0 H3)).
Cut (mem x (union s0 s'))=false;Intros.
Rewrite (fold_add st (fold f (inter s0 s') i) H H0 H4).
Rewrite (fold_add st (fold f s' i) H H0 H1).
Rewrite H2;Auto.
Rewrite union_mem;Rewrite H3; Rewrite H1;Auto.
Cut (subset empty s')=true;Intros.
Rewrite (fold_equal st i H H0 (inter_subset_equal H1)).
Do 2 Rewrite (fold_empty st);Apply fold_equal with eqA:=(eq A);Auto.
Apply union_subset_equal;Auto.
Apply subset_mem_1;Intros.
Rewrite empty_mem in H1;Absurd true=false;Auto with bool.
Qed.

Lemma union_inter_cardinal: 
 (s,s':t)(cardinal (union s s'))+(cardinal (inter s s'))
  = (cardinal s)+(cardinal s').
Proof.
Intros.
Do 4 Rewrite cardinal_fold.
Do 2 Rewrite <- fold_plus.
Apply fold_union_inter;Auto.
Qed.

Lemma fold_union: 
 (A:Set)(f:elt->A->A)(i:A)(compat_op E.eq (eq A) f) -> (transpose (eq A) f) -> 
 (s,s':t)((x:elt)(andb (mem x s) (mem x s'))=false) -> 
 (fold f (union s s') i)=(fold f s (fold f s' i)).
Proof.
Intros.
Assert st:= (gen_st A).
Rewrite <- (fold_union_inter i H H0 s s').
Cut (equal (inter s s') empty)=true;Intros.
Rewrite (fold_equal st i H H0 H2). 
Rewrite (fold_empty st);Auto.
Apply equal_mem_1;Intros.
Rewrite inter_mem; Rewrite empty_mem;Auto.
Qed.

Lemma union_cardinal: 
 (s,s':t)((x:elt)(andb (mem x s) (mem x s'))=false) -> 
 (cardinal (union s s'))=(cardinal s)+(cardinal s').
Proof.
Intros.
Do 3 Rewrite cardinal_fold.
Rewrite fold_union;Auto.
Apply fold_plus;Auto.
Qed.

(*s Properties of [diff] *)

Lemma diff_subset: 
 (s,s':t)(subset (diff s s') s)=true.
Proof.
Intros.
Apply subset_mem_1;Intros.
Rewrite diff_mem in H.
Elim (andb_prop ? ? H);Auto.
Qed.

Lemma diff_subset_equal:
 (s,s':t)(subset s s')=true->(equal (diff s s') empty)=true.
Proof.
Intros.
Apply equal_mem_1;Intros.
Rewrite empty_mem.
Rewrite diff_mem.
Generalize (!subset_mem_2 ?? H a).
Case (mem a s);Simpl;Intros;Auto.
Rewrite H0;Auto.
Qed.

Lemma remove_inter_singleton: 
 (s:t)(x:elt)(equal (remove x s) (diff s (singleton x)))=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Rewrite diff_mem.
Elim (ME.eq_dec x a); Intros.
Rewrite <- (mem_eq (remove x s) a0).
Rewrite <- (mem_eq s a0).
Rewrite <- (mem_eq (singleton x) a0).
Rewrite remove_mem_1;Rewrite singleton_mem_1;Rewrite andb_b_false;Auto.
Rewrite singleton_mem_2;Auto;Simpl;Rewrite andb_b_true;Auto with set.
Qed.

Lemma diff_inter_empty:
 (s,s':t)(equal (inter (diff s s') (inter s s')) empty)=true. 
Proof.
Intros;Apply equal_mem_1;Intros.
Rewrite empty_mem;Do 2 Rewrite inter_mem;Rewrite diff_mem.
Case (mem a s);Case (mem a s');Simpl;Auto.
Qed.

Lemma diff_inter_all: 
(s,s':t)(equal (union (diff s s') (inter s s')) s)=true.
Proof.
Intros;Apply equal_mem_1;Intros.
Rewrite union_mem;Rewrite inter_mem;Rewrite diff_mem.
Case (mem a s);Case (mem a s');Simpl;Auto.
Qed.

Lemma fold_diff_inter: 
 (A:Set)(f:elt->A->A)(i:A)(compat_op E.eq (eq A) f) -> (transpose (eq A) f) ->
 (s,s':t)(fold f (diff s s') (fold f (inter s s') i))=(fold f s i).
Proof.
Intros.
Assert st := (gen_st A).
Rewrite <- (fold_union_inter i H H0 (diff s s') (inter s s')).
Rewrite (fold_equal st i H H0 (diff_inter_empty s s')).
Rewrite (fold_empty st).
Apply fold_equal with eqA:=(eq A);Auto.
Apply diff_inter_all.
Qed.

Lemma diff_inter_cardinal: 
 (s,s':t)(cardinal (diff s s'))+(cardinal (inter s s'))=(cardinal s).
Proof.
Intros.
Do 3 Rewrite cardinal_fold.
Rewrite <- fold_plus.
Apply fold_diff_inter; Auto.
Qed.

Lemma subset_cardinal: 
 (s,s':t)(subset s s')=true -> (le (cardinal s) (cardinal s')).
Proof.
Intros.
Rewrite <- (diff_inter_cardinal s' s).
Rewrite (equal_cardinal (inter_sym s' s)).
Rewrite (equal_cardinal (inter_subset_equal H)); Auto with arith.
Qed.

(*s Properties of [for_all] *)

Section For_all.

Variable f : elt->bool.
Variable Comp : (compat_bool E.eq f).

Local Comp' : (compat_bool E.eq [x](negb (f x))).
Proof.
Generalize Comp; Unfold compat_bool; Intros; Apply (f_equal ?? negb);Auto.
Qed.

Lemma for_all_mem_1: 
 (s:t)((x:elt)(mem x s)=true->(f x)=true) -> (for_all f s)=true.
Proof.
Intros.
Rewrite for_all_filter; Auto.
Rewrite is_empty_equal_empty.
Apply equal_mem_1;Intros.
Rewrite filter_mem; Auto.
Rewrite empty_mem.
Generalize (H a); Case (mem a s);Intros;Auto.
Rewrite H0;Auto.
Qed.

Lemma for_all_mem_2: 
 (s:t)(for_all f s)=true -> (x:elt)(mem x s)=true -> (f x)=true. 
Proof.
Intros.
Rewrite for_all_filter in H; Auto.
Rewrite is_empty_equal_empty in H.
Generalize (equal_mem_2 H x).
Rewrite filter_mem; Auto.
Rewrite empty_mem.
Rewrite H0; Simpl;Intros.
Replace true with (negb false);Auto;Apply negb_sym;Auto.
Qed.

Lemma for_all_mem_3: 
 (s:t)(x:elt)(mem x s)=true -> (f x)=false -> (for_all f s)=false.
Proof.
Intros.
Apply (bool_eq_ind (for_all f s));Intros;Auto.
Rewrite for_all_filter in H1; Auto.
Rewrite is_empty_equal_empty in H1.
Generalize (equal_mem_2 H1 x).
Rewrite filter_mem; Auto.
Rewrite empty_mem.
Rewrite H.
Rewrite H0.
Simpl;Auto.
Qed.

Lemma for_all_mem_4: 
 (s:t)(for_all f s)=false -> {x:elt | (mem x s)=true /\ (f x)=false}.
Intros.
Rewrite for_all_filter in H; Auto.
Elim (choose_mem_3 H);Intros;Elim p;Intros.
Exists x.
Rewrite filter_mem in H1; Auto.
Elim (andb_prop ? ? H1).
Split;Auto.
Replace false with (negb true);Auto;Apply negb_sym;Auto.
Qed.

End For_all.

(*s Properties of [exists] *)

Section Exists.

Variable f : elt->bool.
Variable Comp : (compat_bool E.eq f).

Local Comp' : (compat_bool E.eq [x](negb (f x))).
Proof.
Generalize Comp; Unfold compat_bool; Intros; Apply (f_equal ?? negb);Auto.
Qed.

Lemma for_all_exists: 
 (s:t)(exists f s)=(negb (for_all [x](negb (f x)) s)).
Proof.
Intros.
Rewrite for_all_filter; Auto.
Rewrite exists_filter; Auto.
Apply (f_equal ? ? negb).
Do 2 Rewrite is_empty_equal_empty.
Apply equal_equal.
Apply equal_mem_1;Intros.
Do 2 (Rewrite filter_mem; Auto).
Rewrite negb_elim;Auto.
Generalize Comp'; Unfold compat_bool; Intros; Apply (f_equal ? ?  negb); Auto.
Qed.

Lemma exists_mem_1: 
 (s:t)((x:elt)(mem x s)=true->(f x)=false) -> (exists f s)=false.
Proof.
Intros.
Rewrite for_all_exists; Auto.
Rewrite for_all_mem_1;Auto with bool.
Intros;Generalize (H x H0);Intros. 
Symmetry;Apply negb_sym;Simpl;Auto.
Qed.

Lemma exists_mem_2: 
 (s:t)(exists f s)=false -> (x:elt)(mem x s)=true -> (f x)=false. 
Proof.
Intros.
Rewrite for_all_exists in H.
Replace false with (negb true);Auto;Apply negb_sym;Symmetry.
Rewrite (for_all_mem_2 1![x](negb (f x)) Comp' 3!s);Simpl;Auto.
Replace true with (negb false);Auto;Apply negb_sym;Auto.
Qed.

Lemma exists_mem_3: 
 (s:t)(x:elt)(mem x s)=true -> (f x)=true -> (exists f s)=true.
Proof.
Intros.
Rewrite for_all_exists.
Symmetry;Apply negb_sym;Simpl.
Apply for_all_mem_3 with x;Auto.
Rewrite H0;Auto.
Qed.

Lemma exists_mem_4: 
 (s:t)(exists f s)=true -> {x:elt | (mem x s)=true /\ (f x)=true}.
Proof.
Intros.
Rewrite for_all_exists in H.
Elim (for_all_mem_4 1![x](negb (f x)) Comp' 3!s);Intros.
Elim p;Intros.
Exists x;Split;Auto.
Replace true with (negb false);Auto;Apply negb_sym;Auto.
Replace false with (negb true);Auto;Apply negb_sym;Auto.
Qed.

End Exists.

Section Sum.


Definition sum := [f:elt -> nat; s:t](fold [x](plus (f x)) s 0). 

Definition compat_nat := [A:Set][eqA:A->A->Prop][f:A->nat]
 (x,x':A)(eqA x x') -> (f x)=(f x').
Hints Unfold compat_nat.

Lemma sum_plus : 
  (f,g:elt ->nat)(compat_nat E.eq f) -> (compat_nat E.eq g) -> 
     (s:t)(sum [x]((f x)+(g x)) s) = (sum f s)+(sum g s).
Proof.
Unfold sum.
Intros f g Hf Hg.
Assert fc : (compat_op E.eq (eq ?) [x:elt](plus (f x))).  Auto.
Assert ft : (transpose (eq ?) [x:elt](plus (f x))). Red; Intros; Omega.
Assert gc : (compat_op E.eq (eq ?) [x:elt](plus (g x))). Auto.
Assert gt : (transpose (eq ?) [x:elt](plus (g x))). Red; Intros; Omega.
Assert fgc : (compat_op E.eq (eq ?) [x:elt](plus ((f x)+(g x)))). Auto.
Assert fgt : (transpose (eq ?) [x:elt](plus ((f x)+(g x)))). Red; Intros; Omega.
Assert st := (gen_st nat).
Intros s;Pattern s; Apply set_ind.
Intros.
Rewrite <- (fold_equal st O fc ft H).
Rewrite <- (fold_equal st O gc gt H).
Rewrite <- (fold_equal st O fgc fgt H); Auto.
Assert fold_add' := [s:t; t:elt](!fold_add s t ?? st).
Intros; Do 3 (Rewrite fold_add';Auto).
Rewrite H0;Simpl;Omega.
Intros; Do 3 Rewrite (fold_empty st);Auto.
Qed.

Lemma filter_equal : (f:elt -> bool)(compat_bool E.eq f) -> 
     (s,s':t)(Equal s s') -> (Equal (filter f s) (filter f s')).
Proof.
Unfold Equal; Split; Intros; Elim (H0 a); Intros; Apply filter_3; EAuto.
Qed.

Lemma add_filter_1 :  (f:elt -> bool)(compat_bool E.eq f) -> 
  (s,s':t)(x:elt) (f x)=true -> (Add x s s') -> (Add x (filter f s) (filter f s')).
Proof.
Unfold Add; Split; Intros; Elim (H1 y); Clear H1; Intros.
Elim H1; [ Auto | Right; EAuto | EAuto ].
Apply filter_3; Auto.
Elim H2; Intros.
Intuition.
Apply H3; Right; EAuto.
Elim H2; Intros.
Rewrite <- H0; Auto.
EAuto.
Qed.

Lemma add_filter_2 :  (f:elt -> bool)(compat_bool E.eq f) -> 
  (s,s':t)(x:elt) (f x)=false -> (Add x s s') -> (Equal (filter f s) (filter f s')).
Proof.
Unfold Add Equal; Split; Intros; Elim (H1 a); Clear H1; Intros.
Elim H1; Intros. 
Absurd true=false; Auto with bool.
Rewrite <- H0. 
Rewrite <- (filter_2 H H2); Auto.
Apply filter_3; EAuto.
Apply H3; Right; EAuto.

Elim H1; Intros. 
Absurd true=false; Auto with bool.
Rewrite <- H0. 
Rewrite <- (filter_2 H H2); Auto.
EAuto.
EAuto.
Qed.

Lemma sum_filter : (f:elt -> bool)(compat_bool E.eq f) -> 
  (s:t)(sum [x](if (f x) then 1 else 0) s) = (cardinal (filter f s)).
Proof.
Unfold sum; Intros f Hf.
Assert st := (gen_st nat).
Assert fold_add' := [s:t; t:elt](!fold_add s t ?? st).
Assert cc : (compat_op E.eq (eq ?) [x:elt](plus (if (f x) then 1 else 0))). 
 Unfold compat_op; Intros.
 Rewrite (Hf x x' H); Auto.
Assert ct : (transpose (eq ?) [x:elt](plus (if (f x) then 1 else 0))).
 Unfold transpose; Intros; Omega.
Intros s;Pattern s; Apply set_ind.
Intros.
Rewrite <- (fold_equal st O  cc ct H).
Rewrite <- (Equal_cardinal (filter_equal Hf (equal_2 H))); Auto.
Intros; Rewrite fold_add'; Auto.
Generalize (!add_filter_1 f Hf s0 (add x s0) x) (!add_filter_2 f Hf s0 (add x s0) x) .
Assert ~(In x (filter f s0)).
 Intro H1; Rewrite (mem_1 (filter_1 Hf H1)) in H; Discriminate H.
Case (f x); Simpl; Intuition.
Rewrite (cardinal_2 H1 (H4 (Add_add s0 x))); Auto.
Rewrite <- (Equal_cardinal (H4 (Add_add s0 x))); Auto.
Intros; Rewrite (fold_empty st);Auto.
Rewrite cardinal_1; Auto.
Unfold Empty; Intuition.
Elim (!empty_1 a); EAuto.
Qed.

Lemma fold_compat : 
  (A:Set)(eqA:A->A->Prop)(st:(Setoid_Theory ? eqA))
  (f,g:elt->A->A)
  (compat_op E.eq eqA f) -> (transpose eqA f) -> 
  (compat_op E.eq eqA g) -> (transpose eqA g) -> 
  (i:A)(s:t)((x:elt)(In x s) -> (y:A)(eqA (f x y) (g x y))) -> 
  (eqA (fold f s i) (fold g s i)).
Proof.
Intros A eqA st f g fc ft gc gt i.
Intro s; Pattern s; Apply set_ind; Intros.
Apply (Seq_trans ?? st) with (fold f s0 i).
Apply fold_equal with eqA:=eqA; Auto.
Rewrite equal_sym; Auto.
Apply (Seq_trans ?? st) with (fold g s0 i).
Apply H0; Intros; Apply H1; Auto.
Elim  (equal_2 H x); Intuition.
Apply fold_equal with eqA:=eqA; Auto.
Apply (Seq_trans ?? st) with (f x (fold f s0 i)).
Apply fold_add with eqA:=eqA; Auto.
Apply (Seq_trans ?? st) with (g x (fold f s0 i)).
Apply H1; Auto with set.
Apply (Seq_trans ?? st) with (g x (fold g s0 i)).
Apply gc; Auto.
Apply Seq_sym; Auto; Apply fold_add with eqA:=eqA; Auto.
Apply (Seq_trans ?? st) with i; [Idtac | Apply Seq_sym; Auto]; Apply fold_empty; Auto.
Qed.

Lemma sum_compat : 
  (f,g:elt->nat)(compat_nat E.eq f) -> (compat_nat E.eq g) -> 
  (s:t)((x:elt)(In x s) -> (f x)=(g x)) -> (sum f s)=(sum g s).
Intros.
Unfold sum; Apply (!fold_compat ? (eq nat)); Auto.
Unfold transpose; Intros; Omega.
Unfold transpose; Intros; Omega.
Qed.

End Sum.

Lemma filter_orb: (f,g:elt->bool)(compat_bool E.eq f) -> (compat_bool E.eq g) ->
  (s:t)(Equal (filter [x:elt](orb (f x) (g x)) s) (union (filter f s) (filter g s))).
Proof.
Intros.
Assert (compat_bool E.eq [x](orb (f x) (g x))).
  Unfold compat_bool; Intros.
  Rewrite (H x y H1).
  Rewrite (H0 x y H1); Auto.
Unfold Equal; Split; Intros.
Assert H3 := (filter_1 H1 H2).
Assert H4 := (filter_2 H1 H2).
Elim (orb_prop ?? H4); Intros; EAuto.
Elim (union_1 H2); Intros. 
Apply filter_3; [ Auto | EAuto | Rewrite (filter_2 H H3); Auto ].
Apply filter_3; [ Auto | EAuto | Rewrite (filter_2 H0 H3); Auto with bool].
Qed.

End MoreProperties.
Hints Unfold compat_nat.

End Properties. 
