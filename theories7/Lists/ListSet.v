(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** A Library for finite sets, implemented as lists 
    A Library with similar interface will soon be available under
    the name TreeSet in the theories/Trees directory *)

(** PolyList is loaded, but not exported.
    This allow to "hide" the definitions, functions and theorems of PolyList
    and to see only the ones of ListSet *)

Require PolyList.

Set Implicit Arguments.
V7only [Implicits nil [1].].

Section first_definitions.

  Variable A : Set.
  Hypothesis Aeq_dec : (x,y:A){x=y}+{~x=y}.

  Definition set := (list A).

  Definition empty_set := (!nil ?) : set.

  Fixpoint set_add [a:A; x:set] : set :=
    Cases x of
    | nil => (cons a nil)
    | (cons a1 x1) => Cases (Aeq_dec a a1) of 
                    | (left _) => (cons a1 x1) 
                    | (right _) => (cons a1 (set_add a x1))
                   end
    end.


  Fixpoint set_mem [a:A; x:set] : bool :=
    Cases x of
    | nil => false
    | (cons a1 x1) => Cases (Aeq_dec a a1) of 
                    | (left _) => true 
                    | (right _) => (set_mem a x1)
                   end
    end.
 
  (** If [a] belongs to [x], removes [a] from [x]. If not, does nothing *)
  Fixpoint set_remove [a:A; x:set] : set :=
    Cases x of
    | nil => empty_set
    | (cons a1 x1) => Cases (Aeq_dec a a1) of 
                    | (left _) => x1 
                    | (right _) => (cons a1 (set_remove a x1))
                   end
    end.

  Fixpoint set_inter [x:set] : set -> set :=
    Cases x of
    | nil => [y]nil
    | (cons a1 x1) => [y]if (set_mem a1 y) 
                      then (cons a1 (set_inter x1 y))
		      else (set_inter x1 y)
    end.

  Fixpoint set_union [x,y:set] : set :=
    Cases y of
    | nil => x
    | (cons a1 y1) => (set_add a1 (set_union x y1))
    end.
        
  (** returns the set of all els of [x] that does not belong to [y] *)
  Fixpoint set_diff [x:set] : set -> set :=
    [y]Cases x of
    | nil => nil
    | (cons a1 x1) => if (set_mem a1 y) 
                      then (set_diff x1 y)
		      else (set_add a1 (set_diff x1 y))
    end.
   

  Definition set_In : A -> set -> Prop := (In 1!A).

  Lemma set_In_dec : (a:A; x:set){(set_In a x)}+{~(set_In a x)}.

  Proof.
    Unfold set_In.
    (*** Realizer set_mem. Program_all. ***)
    Induction x.
    Auto.
    Intros a0 x0 Ha0. Case (Aeq_dec a a0); Intro eq.
    Rewrite eq; Simpl; Auto with datatypes.
    Elim Ha0.
    Auto with datatypes.
    Right; Simpl; Unfold not; Intros [Hc1 | Hc2 ]; Auto with datatypes.
  Qed.

  Lemma set_mem_ind : 
    (B:Set)(P:B->Prop)(y,z:B)(a:A)(x:set)
      ((set_In a x) -> (P y))
       ->(P z)
       ->(P (if (set_mem a x) then y else z)).

  Proof.
    Induction x; Simpl; Intros.
    Assumption.
    Elim (Aeq_dec a a0); Auto with datatypes.
  Qed.

  Lemma set_mem_ind2 : 
    (B:Set)(P:B->Prop)(y,z:B)(a:A)(x:set)
      ((set_In a x) -> (P y))
       ->(~(set_In a x) -> (P z))
       ->(P (if (set_mem a x) then y else z)).

  Proof.
    Induction x; Simpl; Intros.
    Apply H0; Red; Trivial.
    Case (Aeq_dec a a0); Auto with datatypes.
    Intro; Apply H; Intros; Auto.
    Apply H1; Red; Intro.
    Case H3; Auto.
  Qed.

 
  Lemma set_mem_correct1 :
    (a:A)(x:set)(set_mem a x)=true -> (set_In a x).
  Proof.
    Induction x; Simpl.
    Discriminate.
    Intros a0 l; Elim (Aeq_dec a a0); Auto with datatypes.
  Qed.

  Lemma set_mem_correct2 :
    (a:A)(x:set)(set_In a x) -> (set_mem a x)=true.
  Proof.
    Induction x; Simpl.
    Intro Ha; Elim Ha.
    Intros a0 l; Elim (Aeq_dec a a0); Auto with datatypes.
    Intros H1 H2 [H3 | H4].
    Absurd a0=a; Auto with datatypes.
    Auto with datatypes.
  Qed.

  Lemma set_mem_complete1 :
    (a:A)(x:set)(set_mem a x)=false -> ~(set_In a x).
  Proof.
    Induction x; Simpl.
    Tauto.
    Intros a0 l; Elim (Aeq_dec a a0).
    Intros; Discriminate H0.
    Unfold not; Intros; Elim H1; Auto with datatypes.
  Qed.

  Lemma set_mem_complete2 :
    (a:A)(x:set)~(set_In a x) -> (set_mem a x)=false.
  Proof.
    Induction x; Simpl.
    Tauto.
    Intros a0 l; Elim (Aeq_dec a a0).
    Intros; Elim H0; Auto with datatypes.
    Tauto.
  Qed.

  Lemma set_add_intro1 : (a,b:A)(x:set) 
    (set_In a x) -> (set_In a (set_add b x)).

  Proof.
    Unfold set_In; Induction x; Simpl.
    Auto with datatypes.
    Intros a0 l H [ Ha0a | Hal ].
    Elim (Aeq_dec b a0); Left; Assumption.
    Elim (Aeq_dec b a0); Right; [ Assumption | Auto with datatypes ].
  Qed.

  Lemma set_add_intro2 : (a,b:A)(x:set) 
    a=b -> (set_In a (set_add b x)).

  Proof.
    Unfold set_In; Induction x; Simpl.
    Auto with datatypes.
    Intros a0 l H Hab.
    Elim (Aeq_dec b a0); 
    [ Rewrite Hab; Intro Hba0; Rewrite Hba0; Simpl; Auto with datatypes
    | Auto with datatypes ].
  Qed.

  Hints Resolve set_add_intro1 set_add_intro2.

  Lemma set_add_intro : (a,b:A)(x:set) 
    a=b\/(set_In a x) -> (set_In a (set_add b x)).
  
  Proof.
    Intros a b x [H1 | H2] ; Auto with datatypes.
  Qed.
 
  Lemma set_add_elim : (a,b:A)(x:set) 
    (set_In a (set_add b x)) -> a=b\/(set_In a x).

  Proof.
    Unfold set_In.
    Induction x.
    Simpl; Intros [H1|H2]; Auto with datatypes.
    Simpl; Do 3 Intro.
    Elim (Aeq_dec b a0).
    Simpl; Tauto.
    Simpl; Intros; Elim H0.
    Trivial with datatypes.
    Tauto.
    Tauto.
  Qed.

  Lemma set_add_elim2 :  (a,b:A)(x:set) 
    (set_In a (set_add b x)) -> ~(a=b) -> (set_In a x).
   Intros a b x H; Case (set_add_elim H); Intros; Trivial.
   Case H1; Trivial.
   Qed.

  Hints Resolve set_add_intro set_add_elim set_add_elim2.

  Lemma set_add_not_empty : (a:A)(x:set)~(set_add a x)=empty_set.
  Proof.
    Induction x; Simpl.
    Discriminate.
    Intros; Elim  (Aeq_dec a a0); Intros; Discriminate.
  Qed.   


  Lemma set_union_intro1 : (a:A)(x,y:set)
    (set_In a x) -> (set_In a (set_union x y)).
  Proof.
    Induction y; Simpl; Auto with datatypes.
  Qed.

  Lemma set_union_intro2 : (a:A)(x,y:set)
    (set_In a y) -> (set_In a (set_union x y)).
  Proof.
    Induction y; Simpl.
    Tauto.
    Intros; Elim H0; Auto with datatypes.
  Qed.

  Hints Resolve set_union_intro2 set_union_intro1.

  Lemma set_union_intro : (a:A)(x,y:set)
    (set_In a x)\/(set_In a y) -> (set_In a (set_union x y)).
  Proof.
    Intros; Elim H; Auto with datatypes.
  Qed.

  Lemma set_union_elim : (a:A)(x,y:set)
    (set_In a (set_union x y)) -> (set_In a x)\/(set_In a y).
  Proof.
    Induction y; Simpl.
    Auto with datatypes.
    Intros.
    Generalize (set_add_elim H0).
    Intros [H1 | H1].
    Auto with datatypes.
    Tauto.
  Qed.

  Lemma set_union_emptyL : (a:A)(x:set)(set_In a (set_union empty_set x)) -> (set_In a x).
    Intros a x H; Case (set_union_elim H); Auto Orelse Contradiction.
  Qed.


  Lemma set_union_emptyR : (a:A)(x:set)(set_In a (set_union x empty_set)) -> (set_In a x).
    Intros a x H; Case (set_union_elim H); Auto Orelse Contradiction.
  Qed.


  Lemma set_inter_intro :  (a:A)(x,y:set)
    (set_In a x) -> (set_In a y) -> (set_In a (set_inter x y)).
  Proof.
    Induction x.
    Auto with datatypes.
    Simpl; Intros a0 l Hrec y [Ha0a | Hal] Hy.
    Simpl; Rewrite Ha0a.
    Generalize (!set_mem_correct1 a y).
    Generalize (!set_mem_complete1 a y).
    Elim (set_mem a y); Simpl; Intros.
    Auto with datatypes.
    Absurd (set_In a y); Auto with datatypes.
    Elim (set_mem a0 y); [ Right; Auto with datatypes | Auto with datatypes].     
  Qed.

  Lemma set_inter_elim1 : (a:A)(x,y:set)
    (set_In a (set_inter x y)) -> (set_In a x).
  Proof.
    Induction x.
    Auto with datatypes.
    Simpl; Intros a0 l Hrec y.
    Generalize (!set_mem_correct1 a0 y).
    Elim (set_mem a0 y); Simpl; Intros.
    Elim H0; EAuto with datatypes.
    EAuto with datatypes.
  Qed.

  Lemma set_inter_elim2 : (a:A)(x,y:set)
    (set_In a (set_inter x y)) -> (set_In a y).
  Proof.
    Induction x.
    Simpl; Tauto.
    Simpl; Intros a0 l Hrec y.
    Generalize (!set_mem_correct1 a0 y).
    Elim (set_mem a0 y); Simpl; Intros.
    Elim H0; [ Intro Hr; Rewrite <- Hr; EAuto with datatypes  | EAuto with datatypes ] .
    EAuto with datatypes.
  Qed.

  Hints Resolve set_inter_elim1 set_inter_elim2.

  Lemma set_inter_elim : (a:A)(x,y:set)
    (set_In a (set_inter x y)) -> (set_In a x)/\(set_In a y).
  Proof.
    EAuto with datatypes.
  Qed. 

  Lemma set_diff_intro : (a:A)(x,y:set)
    (set_In a x) -> ~(set_In a y) -> (set_In a (set_diff x y)).
  Proof.
    Induction x.
    Simpl; Tauto.
    Simpl; Intros a0 l Hrec y [Ha0a | Hal] Hay.
    Rewrite Ha0a; Generalize (set_mem_complete2 Hay).
    Elim (set_mem a y); [ Intro Habs; Discriminate Habs | Auto with datatypes ].
    Elim (set_mem a0 y); Auto with datatypes.
  Qed.

  Lemma set_diff_elim1 : (a:A)(x,y:set)
    (set_In a (set_diff x y)) -> (set_In a x).
  Proof.
    Induction x.
    Simpl; Tauto.
    Simpl; Intros a0 l Hrec y; Elim (set_mem a0 y).
    EAuto with datatypes.
    Intro; Generalize (set_add_elim  H).
    Intros [H1 | H2]; EAuto with datatypes.
  Qed.

  Lemma set_diff_elim2 : (a:A)(x,y:set)
    (set_In a (set_diff x y)) -> ~(set_In a y).
  Intros a x y; Elim x; Simpl.
  Intros; Contradiction.
  Intros a0 l Hrec. 
  Apply set_mem_ind2; Auto.
  Intros H1 H2; Case (set_add_elim H2); Intros; Auto.
  Rewrite H; Trivial.
  Qed.

  Lemma set_diff_trivial : (a:A)(x:set)~(set_In a (set_diff x x)).
  Red; Intros a x H.
  Apply (set_diff_elim2 H).
  Apply (set_diff_elim1 H).
  Qed.

Hints Resolve set_diff_intro set_diff_trivial.


End first_definitions.

Section other_definitions.

  Variables A,B : Set.

  Definition set_prod : (set A) -> (set B) -> (set A*B) := (list_prod 1!A 2!B).

  (** [B^A], set of applications from [A] to [B] *)
  Definition set_power : (set A) -> (set B) -> (set (set A*B)) := 
    (list_power 1!A 2!B).

  Definition set_map : (A->B) -> (set A) ->  (set B) := (map 1!A 2!B).

  Definition set_fold_left : (B -> A -> B) -> (set A) -> B -> B := 
     (fold_left 1!B 2!A).

  Definition set_fold_right : (A -> B -> B) -> (set A) -> B -> B  := 
     [f][x][b](fold_right f b x).

 
End other_definitions.

V7only [Implicits nil [].].
Unset Implicit Arguments.
