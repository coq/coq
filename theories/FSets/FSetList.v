(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(** This file propose an implementation of the AbstractSet non-dependant 
    interface by strictly ordered list. *)

Require Export FSetInterface.

Set Implicit Arguments.

(* Usual syntax for lists. 
   CAVEAT: the Coq cast "::" will no longer be available. *)
Notation "[]" := (nil ?) (at level 1).
Notation "a :: l" := (cons a l) (at level 1, l at next level).

(** In a first time, we provide sets as lists which are not necessarily sorted.
   The specs are proved under the additional condition of being sorted. 
   And the functions outputting sets are proved to preserve this invariant. *)

Module Raw [X : OrderedType].
 
  Module E := X.
  Module ME := MoreOrderedType X.

  Definition elt := E.t.
  Definition t := (list elt).

  Definition empty : t := [].

  Definition is_empty : t -> bool := [l]if l then true else [_,_]false.

  (** The set operations. *)

  Fixpoint mem [x:elt; s:t] : bool := Cases s of
      nil => false 
    | (cons y l) => Cases  (E.compare x y) of 
         (Lt _) => false
       | (Eq _) => true
       | (Gt _) => (mem x l)
       end
    end.

  Fixpoint add [x:elt; s:t] : t := Cases s of 
     nil => x::[]
   | (cons y l) => Cases (E.compare x y) of 
         (Lt _) => x::s
       | (Eq _) => s
       | (Gt _) => y::(add x l)
     end 
  end.

  Definition singleton : elt -> t := [x] x::[]. 

  Fixpoint remove [x:elt; s:t] : t := Cases s of 
     nil => []
   | (cons y l) => Cases (E.compare x y) of 
         (Lt _) => s
       | (Eq _) => l
       | (Gt _) => y::(remove x l)
     end 
  end.  
  
  Fixpoint union [s:t] : t -> t := Cases s of 
    nil => [s']s'
  | (cons x l) => 
       Fix union_aux { union_aux / 1 : t -> t := [s']Cases s' of 
           nil => s
         | (cons x' l') => Cases (E.compare x x') of 
              (Lt _ ) => x::(union l s')
            | (Eq _ ) => x::(union l l')
            | (Gt _) => x'::(union_aux l')
            end
         end}
   end.      

  Fixpoint inter [s:t] : t -> t := Cases s of 
    nil => [_] []
  | (cons x l) => 
       Fix inter_aux { inter_aux / 1 : t -> t := [s']Cases s' of 
           nil => []
         | (cons x' l') => Cases (E.compare x x') of 
              (Lt _ ) => (inter l s')
            | (Eq _ ) => x::(inter l l')
            | (Gt _) => (inter_aux l')
            end
         end}
   end.  
  
  Fixpoint diff [s:t] : t -> t := Cases s of 
    nil => [_] []
  | (cons x l) => 
       Fix diff_aux { diff_aux / 1 : t -> t := [s']Cases s' of 
           nil => s
         | (cons x' l') => Cases (E.compare x x') of 
              (Lt _ ) => x::(diff l s')
            | (Eq _ ) => (diff l l')
            | (Gt _) => (diff_aux l')
            end
         end}
   end.  
   
  Fixpoint equal [s:t] : t -> bool := [s':t]Cases s s' of 
    nil nil => true
  | (cons x l) (cons x' l') => Cases (E.compare x x') of 
       (Eq _) => (equal l l') 
     | _ => false 
    end
  | _ _ => false 
  end.

  Fixpoint subset [s,s':t] : bool := Cases s s' of 
    nil _ => true
  | (cons x l) (cons x' l') => Cases (E.compare x x') of 
       (Lt _) => false 
     | (Eq _) => (subset l l') 
     | (Gt _) => (subset s l')
    end
  | _ _ => false 
  end.

  Fixpoint fold [B:Set; f:elt->B->B; s:t] : B -> B := [i]Cases s of 
    nil => i
  | (cons x l) => (f x (fold f l i))
  end.  

  Fixpoint filter [f:elt->bool; s:t] : t := Cases s of 
    nil => []
  | (cons x l) => if (f x) then x::(filter f l) else (filter f l)
  end.  

  Fixpoint for_all [f:elt->bool; s:t] : bool := Cases s of 
    nil => true
  | (cons x l) => if (f x) then (for_all f l) else false
  end.  
 
  Fixpoint exists [f:elt->bool; s:t] : bool := Cases s of 
    nil => false
  | (cons x l) => if (f x) then true else (exists f l)
  end.

  Fixpoint partition [f:elt->bool; s:t] : t*t := Cases s of 
     nil => ([],[])
  | (cons x l) => let (s1,s2) = (partition f l) in 
                         if (f x) then (x::s1,s2) else (s1,x::s2)
  end.

  Definition cardinal : t -> nat := [s](fold [_]S s O).

  Definition elements : t -> (list elt) := [x]x.

  Definition min_elt : t -> (option elt) := [s]Cases s of 
     nil => (None ?)
   | (cons x _) => (Some ? x)
  end.

  Fixpoint max_elt  [s:t] : (option elt) := Cases s of 
    nil => (None ?) 
   | (cons x nil) => (Some ? x) 
   | (cons _ l) => (max_elt l)
  end.

  Definition choose := min_elt.

  (** Proofs of set operation specifications. *)

  Definition In : elt -> t -> Prop := (InList E.eq).
  Notation "'Sort' l" := (sort E.lt l) (at level 10, l at level 8).
  Notation "'Inf' x l" := (lelistA E.lt x l) (at level 10, x,l at level 8).
  Notation "'In' x l" := (InList E.eq x l) (at level 10, x,l at level 8).

  Definition Equal := [s,s'](a:elt)(In a s)<->(In a s').
  Definition Subset := [s,s'](a:elt)(In a s)->(In a s').
  Definition Add := [x:elt;s,s':t](y:elt)(In y s') <-> ((E.eq y x)\/(In y s)).
  Definition Empty := [s](a:elt)~(In a s).
  Definition For_all := [P:elt->Prop; s:t](x:elt)(In x s)->(P x).
  Definition Exists := [P:elt->Prop; s:t](EX x:elt | (In x s)/\(P x)).

  Definition In_eq: (s:t)(x,y:elt)(E.eq x y) -> (In x s) -> (In y s) := ME.In_eq.
  Definition Inf_lt : (s:t)(x,y:elt)(E.lt x y) -> (Inf y s) -> (Inf x s) := ME.Inf_lt.
  Definition Inf_eq : (s:t)(x,y:elt)(E.eq x y) -> (Inf y s) -> (Inf x s) := ME.Inf_eq.
  Definition In_sort : (s:t)(x,a:elt)(Inf a s) -> (In x s) -> (Sort s) -> (E.lt a x) := ME.In_sort.
  Hints Resolve Inf_lt Inf_eq. 
  Hints Immediate In_eq.

  Lemma mem_1: (s:t)(Hs:(Sort s))(x:elt)(In x s) -> (mem x s)=true. 
  Proof.
  Induction s; Intros.
  Inversion H.
  Inversion_clear Hs.
  Inversion_clear H0.
  Simpl; Replace E.compare with X.compare; Auto.
  Elim (!ME.elim_compare_eq x a); [Intros A B; Rewrite B; Auto | Auto].
  Simpl; Replace E.compare with X.compare; Auto.
  Elim (!ME.elim_compare_gt x a); [Intros A B; Rewrite B; Auto | Auto].
  EApply In_sort; EAuto.
  Qed.

  Lemma mem_2: (s:t)(x:elt)(mem x s)=true -> (In x s).
  Proof.
  Induction s. 
  Intros; Inversion H.
  Intros a l Hrec x.
  Simpl; Elim (E.compare x a); Ground.
  Inversion H.
  Qed.

  Lemma add_Inf : (s:t)(x,a:elt)(Inf a s)->(E.lt a x)->(Inf a (add x s)).
  Proof.
  Induction s.  
  Simpl; Intuition.
  Simpl; Intros; Case (E.compare x a); Intuition; Inversion H0; Intuition.
  Qed.
  Hints Resolve add_Inf.
  
  Lemma add_sort : (s:t)(Hs:(Sort s))(x:elt)(Sort (add x s)).
  Proof.
  Induction  s.
  Simpl; Intuition.
  Simpl; Intros; Case (E.compare x a); Intuition; Inversion_clear Hs; Auto.
  Qed. 

  Lemma add_1 : (s:t)(Hs:(Sort s))(x:elt)(In x (add x s)).
  Proof.
  Induction s. 
  Simpl; Intuition.
  Simpl; Intros; Case (E.compare x a); Intuition; Inversion_clear Hs; Ground.
  Qed.

  Lemma add_2 : (s:t)(Hs:(Sort s))(x,y:elt)(In y s) -> (In y (add x s)).
  Proof.
  Induction s. 
  Simpl; Intuition.
  Simpl; Intros; Case (E.compare x a); Intuition.
  Inversion_clear Hs; Inversion_clear H0; EAuto.
  Qed.

  Lemma add_3 : (s:t)(Hs:(Sort s))(x,y:elt)
      ~(E.eq x y) -> (In y (add x s)) -> (In y s).
  Proof.
  Induction s. 
  Simpl; Intuition.
  Inversion_clear H0; Ground; Absurd (E.eq x y); Auto.
  Simpl; Intros a l Hrec Hs x y; Case (E.compare x a); Intros; 
   Inversion_clear H0; Inversion_clear Hs; Ground; Absurd (E.eq x y); Auto.
  Qed.

  Lemma remove_Inf : (s:t)(Hs:(Sort s))(x,a:elt)(Inf a s)->
  (Inf a (remove x s)).
  Proof.
  Induction s.  
  Simpl; Intuition.
  Simpl; Intros; Case (E.compare x a); Intuition; Inversion_clear H0; Ground.
  Inversion_clear Hs; Ground; EAuto.
  Qed.
  Hints Resolve remove_Inf.

  Lemma remove_sort : (s:t)(Hs:(Sort s))(x:elt)(Sort (remove x s)).
  Proof.
  Induction  s.
  Simpl; Intuition.
  Simpl; Intros; Case (E.compare x a); Intuition; Inversion_clear  Hs; Auto.
  Qed. 

  Lemma remove_1 : (s:t)(Hs:(Sort s))(x:elt)~(In x (remove x s)).
  Proof.
  Induction s. 
  Simpl; Red; Intros; Inversion H.
  Simpl; Intros; Case (E.compare x a); Intuition; Inversion_clear Hs. 
  Inversion_clear H0.
  Absurd (E.eq x a); Auto. 
  Absurd (E.lt a x); Auto; EApply In_sort; EAuto.
  Absurd (E.lt a x); Auto; EApply In_sort; EAuto.
  Inversion_clear H0; Ground. 
  Absurd (E.eq x a); Auto.
  Qed.

  Lemma remove_2 : (s:t)(Hs:(Sort s))(x,y:elt) 
      ~(E.eq x y) -> (In y s) -> (In y (remove x s)).
  Proof.
  Induction s. 
  Simpl; Intuition.
  Simpl; Intros; Case (E.compare x a); Intuition; 
    Inversion_clear Hs; Inversion_clear H1; Auto. 
  Absurd (E.eq x y); EAuto. 
  Qed.

  Lemma remove_3 : (s:t)(Hs:(Sort s))(x,y:elt)(In y (remove x s)) -> (In y s).
  Proof.
  Induction s. 
  Simpl; Intuition.
  Simpl; Intros a l Hrec Hs x y; Case (E.compare x a); Intuition.
  Inversion_clear Hs; Inversion_clear H; Ground.
  Qed.
  
  Lemma singleton_sort : (x:elt)(Sort (singleton x)).
  Proof.
  Unfold singleton; Simpl; Ground.
  Qed.

  Lemma singleton_1 : (x,y:elt)(In y (singleton x)) -> (E.eq x y).
  Proof.
  Unfold singleton; Simpl; Intuition.
  Inversion_clear H; Auto; Inversion H0.
  Qed. 

  Lemma singleton_2 : (x,y:elt)(E.eq x y) -> (In y (singleton x)).
  Proof.
  Unfold singleton; Simpl; Intuition.
  Qed. 

  Tactic Definition DoubleInd := 
    Induction s; 
    [Simpl; Auto; Try Solve [ Intros; Inversion H ] |
     Intros x l Hrec; 
     Induction s'; 
     [Simpl; Auto; Try Solve [ Intros; Inversion H ] | 
      Intros x' l' Hrec' Hs Hs'; Inversion Hs; Inversion Hs'; Subst; Simpl]].

  Lemma union_Inf : (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(a:elt) 
      (Inf a s) -> (Inf a s') -> (Inf a (union s s')).
  Proof.
  DoubleInd.
  Intros i His His'; Inversion_clear His; Inversion_clear His'.
  Case (E.compare x x'); Ground.
  Qed.
  Hints Resolve union_Inf.
 
  Lemma union_sort : (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(Sort (union s s')).
  Proof.
  DoubleInd; Case (E.compare x x'); Intuition; Constructor; Auto.
  EAuto.
  Change (Inf x' (union x::l l')); Ground.
  Qed.  
  
  Lemma union_1 : (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(x:elt) 
     (In x (union s s')) -> (In x s)\/(In x s').
  Proof.
  DoubleInd; Case (E.compare x x'); Intuition; Inversion_clear H; Intuition.
  Elim (Hrec (x'::l') H1 Hs' x0); Intuition.
  Elim (Hrec l' H1 H5 x0); Intuition.
  Elim (H0 x0); Intuition.
  Qed.

  Lemma union_2 : (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(x:elt) 
     (In x s) -> (In x (union s s')).
  Proof.
  DoubleInd.
  Intros i Hi; Case (E.compare x x'); Intuition; Inversion_clear Hi; Auto.
  Qed.

  Lemma union_3 : (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(x:elt) 
     (In x s') -> (In x (union s s')).
  Proof.
  DoubleInd. 
  Intros i Hi; Case (E.compare x x'); Inversion_clear Hi; Intuition; EAuto.
  Qed.
    
  Lemma inter_Inf : (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(a:elt) 
      (Inf a s) -> (Inf a s') -> (Inf a (inter s s')).
  Proof.
  DoubleInd.
  Intros i His His'; Inversion His; Inversion His'; Subst.
  Case (E.compare x x'); Intuition; EAuto.
  Qed.
  Hints Resolve inter_Inf. 

  Lemma inter_sort : (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(Sort (inter s s')).
  Proof.
  DoubleInd; Case (E.compare x x'); EAuto.
  Qed.  
  
  Lemma inter_1 : (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(x:elt) 
     (In x (inter s s')) -> (In x s).
  Proof.
  DoubleInd; Case (E.compare x x'); Intuition.
  EAuto. 
  Inversion_clear H; EAuto.
  Qed.

  Lemma inter_2 : (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(x:elt) 
     (In x (inter s s')) -> (In x s').
  Proof.
  DoubleInd; Case (E.compare x x'); Intuition; Inversion_clear H; EAuto. 
  Qed.

  Lemma inter_3 : (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(x:elt) 
     (In x s) -> (In x s') -> (In x (inter s s')).
  Proof.
  DoubleInd.
  Intros i His His'; Elim (E.compare x x'); Intuition.

  Inversion_clear His. 
  Absurd (E.lt i x); EAuto.
  Apply In_sort with (x'::l'); Auto.
  Constructor; EApply ME.eq_lt; EAuto.
  EApply In_eq; EAuto.
  EApply In_eq; EAuto.

  Inversion_clear His; [ EAuto | Inversion_clear His' ]; EAuto.

  Change (In i (inter x::l l')). 
  Inversion_clear His'.
  Absurd (E.lt i x'); EAuto.
  Apply In_sort with (x::l); Auto. 
  Constructor; EApply ME.eq_lt; EAuto.
  EApply In_eq; EAuto.
  EApply In_eq; EAuto.
  Qed.

  Lemma diff_Inf : (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(a:elt) 
      (Inf a s) -> (Inf a s') -> (Inf a (diff s s')).
  Proof.
  DoubleInd.
  Intros i His His'; Inversion His; Inversion His'.
  Case (E.compare x x'); Intuition;EAuto.
  Qed.
  Hints Resolve diff_Inf. 

  Lemma diff_sort : (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(Sort (diff s s')).
  Proof.
  DoubleInd; Case (E.compare x x'); EAuto.
  Qed.  
  
  Lemma diff_1 : (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(x:elt) 
     (In x (diff s s')) -> (In x s).
  Proof.
  DoubleInd; Case (E.compare x x'); Intuition.
  Inversion_clear H;  EAuto.
  EAuto.
  Qed.

  Lemma diff_2 : (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(x:elt) 
     (In x (diff s s')) -> ~(In x s').
  Proof.
  DoubleInd.
  Intros; Intro Abs; Inversion Abs. 
  Case (E.compare x x'); Intuition.

  Inversion_clear H.
  Absurd (E.lt x x); EAuto. 
  Apply In_sort with (x'::l'); Auto. 
  EApply In_eq; EAuto.
  EAuto.
  
  Inversion_clear H3.
  Generalize (diff_1 H1 H5 H); Intros. 
  Absurd (E.lt x x0); EAuto.
  Apply In_sort with l; EAuto.
  EAuto.
  
  Inversion_clear H3. 
  Generalize (diff_1 Hs H5 H); Intros. 
  Absurd (E.lt x' x'); EAuto.
  Apply In_sort with (x::l); Auto.
  EApply In_eq; EAuto.
  EAuto.  
  Qed.

  Lemma diff_3 : (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(x:elt) 
     (In x s) -> ~(In x s') -> (In x (diff s s')).
  Proof.
  DoubleInd.
  Intros i His His'; Elim (E.compare x x'); Intuition; Inversion_clear His.
  EAuto.
  EAuto.
  Elim His'; EAuto.
  EAuto.
  Qed.  

  Lemma equal_1: (s,s':t)(Hs:(Sort s))(Hs':(Sort s')) 
     (Equal s s') -> (equal s s')=true.
  Proof.
  Induction s; Unfold Equal.
  Intro s'; Case s'; Auto.
  Simpl; Intuition.
  Elim (H e); Intros; Assert A : (In e []); Auto; Inversion A.
  Intros x l Hrec s'.
  Case s'.
  Intros; Elim (H x); Intros; Assert A : (In x []); Auto; Inversion A.
  Intros x' l' Hs Hs'; Inversion Hs; Inversion Hs'; Subst.
  Simpl; Case (E.compare x); Intros; Auto.

  Elim (H  x); Intros.
  Assert A : (In x x'::l'); Auto; Inversion_clear A.
  Absurd (E.eq x x'); EAuto.
  Absurd (E.lt x' x); Auto.
  Apply In_sort with l';EAuto.
  
  Apply Hrec; Intuition; Elim (H a); Intros.
  Assert A : (In a x'::l'); Auto; Inversion_clear A; Auto.
  Absurd (E.lt x' x); Auto. 
  Apply In_sort with l;Auto; 
    [ Apply Inf_eq with x;Auto | Apply In_eq with a; EAuto ].
  Assert A : (In a x::l); Auto; Inversion_clear A; Auto.
  Absurd (E.lt x x'); Auto. 
  Apply In_sort with l';Auto; 
    [ Apply Inf_eq with x';Auto | Apply In_eq with a; EAuto ].

  Elim (H  x'); Intros.
  Assert A : (In x' x::l); Auto; Inversion_clear A.
  Absurd (E.eq x' x); EAuto.
  Absurd (E.lt x x'); Auto.
  Apply In_sort with l;EAuto.
  Qed.

  Lemma equal_2: (s,s':t)(equal s s')=true -> (Equal s s').
  Proof.
  Induction s; Unfold Equal.
  Intro s'; Case s'; Intros.
  Intuition.
  Simpl in H; Discriminate H.
  Intros x l Hrec s'.
  Case s'.
  Intros; Simpl in H; Discriminate H.
  Intros x' l'; Simpl; Case (E.compare x); Intros; Auto.
  Discriminate H.
  Elim (Hrec l' H a); Intuition; Inversion_clear H2; EAuto.
  Discriminate H.  
  Qed.  
  
  Lemma subset_1: (s,s':t)(Hs:(Sort s))(Hs':(Sort s')) 
     (Subset s s') -> (subset s s')=true.
  Proof.
  Intros s s'; Generalize s' s; Clear s s'.
  Induction s'; Unfold Subset.
  Intro s; Case s; Auto.
  Intros; Elim (H e); Intros; Assert A : (In e []); Auto; Inversion A. 
  Intros x' l' Hrec s; Case s.
  Simpl; Auto.
  Intros x l Hs Hs'; Inversion Hs; Inversion Hs'; Subst.
  Simpl; Case (E.compare x); Intros; Auto.

  Assert A : (In x x'::l'); Auto; Inversion_clear A.
  Absurd (E.eq x x'); EAuto.
  Absurd (E.lt x' x); Auto.
  Apply In_sort with l';EAuto.
  
  Apply Hrec; Intuition.
  Assert A : (In a x'::l'); Auto; Inversion_clear A; Auto.
  Absurd (E.lt x' x); Auto. 
  Apply In_sort with l;Auto; [ Apply Inf_eq with x;Auto | Apply In_eq with a; EAuto ].

  Apply Hrec; Intuition.
  Assert A : (In a x'::l'); Auto; Inversion_clear A; Auto.
  Inversion_clear H0.  
  Absurd (E.lt x' x); EAuto.
  Absurd (E.lt x x'); Auto. 
  Apply In_sort with l;EAuto.
  Qed.

  Lemma subset_2: (s,s':t)(subset s s')=true -> (Subset s s').
  Proof.
  Intros s s'; Generalize s' s; Clear s s'.
  Induction s'; Unfold Subset.
  Intro s; Case s; Auto.
  Simpl; Intros; Discriminate H.
  Intros x' l' Hrec s; Case s.
  Intros; Inversion H0.
  Intros x l; Simpl; Case (E.compare x); Intros; Auto.
  Discriminate H.  
  Inversion_clear H0; EAuto.
  EAuto.
  Qed.  
  
  Lemma empty_sort : (Sort empty).
  Proof.
  Unfold empty; Constructor.
  Qed.

  Lemma empty_1 : (Empty empty).
  Proof.
  Unfold Empty empty; Intuition; Inversion H.
  Qed. 

  Lemma is_empty_1 : (s:t)(Empty s) -> (is_empty s)=true.
  Proof.
  Unfold Empty; Intro s; Case s; Simpl; Intuition.
  Elim (H e); Auto.
  Qed.
  
  Lemma is_empty_2 : (s:t)(is_empty s)=true -> (Empty s). 
  Proof.
  Unfold Empty; Intro s; Case s; Simpl; Intuition; Inversion H0.
  Qed.

  Lemma elements_1: (s:t)(x:elt)(In x s) -> (InList E.eq x (elements s)).
  Proof.
  Unfold elements; Auto.
  Qed.

  Lemma elements_2: (s:t)(x:elt)(InList E.eq x (elements s)) -> (In x s).
  Proof. 
  Unfold elements; Auto.
  Qed.
 
  Lemma elements_3: (s:t)(Hs:(Sort s))(sort E.lt (elements s)).  
  Proof. 
  Unfold elements; Auto.
  Qed.

  Lemma min_elt_1: (s:t)(x:elt)(min_elt s) = (Some ? x) -> (In x s). 
  Proof.
  Intro s; Case s; Simpl; Intros; Inversion H; Auto.
  Qed.  

  Lemma min_elt_2: (s:t)(Hs:(Sort s))(x,y:elt)
      (min_elt s) = (Some ? x) -> (In y s) -> ~(E.lt y x). 
  Proof.
  Induction s; Simpl.
  Intros; Inversion H.
  Intros a l; Case l; Intros; Inversion H0; Inversion_clear H1; Subst. 
  EAuto.
  Inversion H2.
  EAuto.
  Inversion_clear Hs.
  Inversion_clear H3.
  Intro; Absurd (E.lt y e); EAuto.
  Qed. 

  Lemma min_elt_3: (s:t)(min_elt s) = (None ?) -> (Empty s).
  Proof.
  Unfold Empty; Intro s; Case s; Simpl; Intuition; Inversion H; Inversion H0.
  Qed.

  Lemma max_elt_1: (s:t)(x:elt)(max_elt s) = (Some ? x) -> (In x s). 
  Proof. 
  Induction s; Simpl.
  Intros; Inversion H.
  Intros x l; Case l; Simpl.
  Intuition.
  Inversion H0; Auto.
  EAuto.
  Qed.
 
  Lemma max_elt_2: (s:t)(Hs:(Sort s))(x,y:elt)
     (max_elt s) = (Some ? x) -> (In y s) -> ~(E.lt x y). 
  Proof.
  Induction s; Simpl.
  Intros; Inversion H.
  Intros x l; Case l; Simpl.
  Intuition.
  Inversion H0; Subst.
  Inversion_clear H1.
  Absurd (E.eq y x0); Auto. 
  Inversion H3.
  Intros; Inversion_clear Hs; Inversion_clear H3; Inversion_clear H1.
  Assert ~(E.lt x0 e).
   EApply H; EAuto.
  Intro.
  Elim H1; Apply E.lt_trans with x; Auto; EApply ME.lt_eq; EAuto.
  EApply H;EAuto.
  Qed. 

  Lemma max_elt_3: (s:t)(max_elt s) = (None ?) -> (Empty s).
  Proof.
  Unfold Empty; Induction s; Simpl.
  Red; Intros; Inversion H0.
  Intros x l; Case l; Simpl; Intros.
  Inversion H0.
  Elim (H H0 e); Auto.
  Qed.

  Definition choose_1:
     (s:t)(x:elt)(choose s)=(Some ? x) -> (In x s)
     := min_elt_1.

  Definition choose_2: (s:t)(choose s)=(None ?) -> (Empty s)
     := min_elt_3.

  Lemma fold_1 : (s:t)(A:Set)(eqA:A->A->Prop)(st:(Setoid_Theory A eqA))(i:A)(f:elt->A->A)
     (Empty s) -> (eqA (fold f s i) i).
  Proof.
  Unfold Empty; Intro s; Case s; Intros; Simpl; Intuition; Elim (H e); Auto.
  Qed.

  Lemma fold_equal : 
     (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(A:Set)(eqA:A->A->Prop)(st:(Setoid_Theory A eqA))
     (i:A)(f:elt->A->A)(compat_op E.eq eqA f) -> (transpose eqA f) -> (Equal s s') ->
     (eqA (fold f s i) (fold f s' i)).
  Proof.
  Induction s; Unfold Equal; Simpl.

  Intro s'; Case s'; Intuition.
  Intros.
  Elim (H1 e); Intuition.
  Assert X : (In e []); Auto; Inversion X.

  Intros x l Hrec s'; Case s'.
  Intros.
  Elim (H1 x); Intuition.
  Assert X : (In x []); Auto; Inversion X.
  Simpl; Intros x' l' Hs Hs' a; Intros.
  Inversion_clear Hs; Inversion_clear Hs'.
  Assert (E.eq x x').
   Assert (In x x'::l').
    Elim (H1 x); Auto.
   Assert (In x' x::l).
    Elim (H1 x'); Auto.
  Inversion_clear H6; Auto.
  Inversion_clear H7; Auto.
  Absurd (E.lt x x').
  Apply ME.lt_not_gt.
  Apply In_sort with l'; EAuto.
  Apply In_sort with l; EAuto.
  Apply H; Auto.
  Apply (Hrec l' H2 H4 a eqA); Auto.
  (* To prove (Equal l l') *)
  Intuition.
  Elim (H1 a0); Intros.
  Assert (In a0 x'::l'). Auto.
  Inversion_clear H10; Auto.
  Intros; Absurd (E.lt x x'); EAuto.
  Apply In_sort with l; EAuto.
  Elim (H1 a0); Intros.
  Assert (In a0 x::l). Auto.
  Inversion_clear H10; Auto.
  Intros; Absurd (E.lt x' x); EAuto.
  Apply In_sort with l'; EAuto.
  Qed.

  Lemma fold_2 : 
     (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(x:elt)(A:Set)(eqA:A->A->Prop)(st:(Setoid_Theory A eqA))
     (i:A)(f:elt->A->A)(compat_op E.eq eqA f) -> (transpose eqA f) -> ~(In x s) -> (Add x s s') ->
     (eqA (fold f s' i) (f x (fold f s i))).
  Proof.
  Induction s; Unfold Add; Simpl.

  Intro s'; Case s'.
  Intros.
  Elim (H2 x); Intuition.
  Assert X : (In x []); Auto; Inversion X.
  Simpl; Intros.
  Inversion_clear Hs'.
  Apply H; Auto.
  Elim (H2 e);Intuition.
  Elim H5; Auto.
  Intros X; Inversion X.
  Apply fold_1; Auto.
  Unfold Empty; Intuition.
  Assert (y:elt)(In y e::l) -> (E.eq y x).
   Intros; Elim (H2 y); Intuition; Inversion H7.
  Assert (E.eq a x); [Ground | Idtac].
  Assert (E.eq e x); [Ground | Idtac].
  Absurd (E.lt a e); EAuto.
  Apply In_sort with l; EAuto. Apply In_eq with a; EAuto.

  Intros x l Hrec s'; Case s'.
  Intros.
  Elim (H2 x0); Intuition.
  Assert X : (In x0 []); Auto; Inversion X.
  Simpl; Intros x' l' Hs Hs' a; Intros.
  Inversion Hs; Inversion Hs'.
  Assert (In a x'::l');[Ground|Idtac].
  (* 2 cases: x'=a or x'<a *)
  (* first, x'=a *)
  Inversion_clear H11.
  Apply H; Auto.
  Change (eqA (fold f l' i) (fold f (x::l) i)).
  Apply (!fold_equal l' (x::l) H9 Hs A eqA); Auto.
  (* To prove that (Equal l' (x::l)) *)
  Unfold Equal.
  Intuition.
  Elim (H2 a2); Intros.
  Elim H13; Auto.
  Intros.
  Absurd (E.lt x' a2); EAuto; Apply In_sort with l'; EAuto.
   Elim (H2 a2); Intros.
  Assert (In a2 x'::l'); Auto.
  Inversion_clear H15; Auto.
  Elim H1; Apply In_eq with a2; EAuto.
 (* second, x'<a *)
  Assert (E.lt x' a).
    Apply In_sort with l'; EAuto.
  Assert ~(E.eq a x).
   Intro; Elim H1; Auto.
  Assert (E.eq x x').
   Assert (In x x'::l').
    Elim (H2 x); Auto.
   Assert (In x' x::l).
    Elim (H2 x'); Intuition.
    Elim H15; Auto.
    Intros; Absurd (E.eq x' a); EAuto.
   Inversion_clear H14; Auto.
   Inversion_clear H15; Auto.
   Absurd (E.lt x x').
   Apply ME.lt_not_gt.
   Apply In_sort with l'; EAuto.
   Apply In_sort with l; EAuto.
  Apply (Seq_trans ? ? st) with (f x (f a (fold f l i))).
  2: Apply H0.
  Apply H; Auto.
  Apply (Hrec l' H5 H9 a A eqA); Clear Hrec; Auto.
  (* To prove (Add a l l') *)
  Intuition.
  Elim (H2 y); Intros.
  Elim H16; Auto; Intros.
  Inversion_clear H18.
  Absurd (E.lt x' y); EAuto; Apply In_sort with l'; EAuto.
  Right; Auto.
  Apply In_eq with a; Auto.
  Elim (H2 y); Intuition.
  Assert (In y x'::l'); Auto.
  Inversion_clear H17; Auto.
  Absurd (E.lt x y); EAuto; Apply In_sort with l; EAuto.
  Qed.

  Lemma cardinal_1 : (s:t)(Empty s) -> (cardinal s)=O.
  Proof.
  Unfold cardinal; Intros; Apply fold_1; Auto.
  Intuition EAuto; Transitivity y; Auto.
  Qed.

  Lemma cardinal_2 : (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(x:elt)
     ~(In x s) -> (Add  x s s') -> (cardinal s') = (S (cardinal s)).
  Proof.
  Unfold cardinal; Intros.
  Assert (compat_op E.eq (eq ?) [_]S).
   Unfold compat_op; Auto.
  Assert (transpose (eq ?) [_:elt]S).
    Unfold transpose; Auto.
  Refine (!fold_2 s s' Hs Hs' x nat (eq ?) ? O [_]S H1 H2 H H0).
  Intuition EAuto; Transitivity y; Auto.
  Qed.

  Lemma filter_Inf : 
    (s:t)(Hs:(Sort s))(x:elt)(f:elt->bool)(Inf x s) -> (Inf x (filter f s)).
  Proof.
  Induction s; Simpl.
  Intuition.  
  Intros x l Hrec Hs a f Ha; Inversion_clear Hs; Inversion Ha.
  Case (f x); [Constructor; Auto | EAuto]. 
  Qed.

  Lemma filter_sort : (s:t)(Hs:(Sort s))(f:elt->bool)(Sort (filter f s)).
  Proof.
  Induction s; Simpl.
  Auto.
  Intros x l Hrec Hs f; Inversion_clear Hs.
  Case (f x); Auto.
  Constructor; Auto.
  Apply filter_Inf; Auto. 
  Qed.

  Lemma filter_1: (s:t)(x:elt)(f:elt->bool)(compat_bool E.eq f) -> 
     (In x (filter f s)) -> (In x s).
  Proof.
  Induction s; Simpl.
  Intros; Inversion H0.
  Intros x l Hrec a f Hf.
  Case (f x); Simpl; Ground.
  Inversion H; Ground.
  Qed.

   Lemma filter_2: 
    (s:t)(x:elt)(f:elt->bool)(compat_bool E.eq f) ->(In x (filter f s)) -> 
    (f x)=true.   
   Proof.
  Induction s; Simpl.
  Intros; Inversion H0.
  Intros x l Hrec a f Hf.
  Generalize (Hf x); Case (f x); Simpl; Ground.
  Inversion H0; Ground.
  Symmetry; Ground.
  Qed.
 
  Lemma filter_3: 
    (s:t)(x:elt)(f:elt->bool)(compat_bool E.eq f) -> 
        (In x s) -> (f x)=true -> (In x (filter f s)).     
  Proof.
  Induction s; Simpl.
  Intros; Inversion H0.
  Intros x l Hrec a f Hf.
  Generalize (Hf x); Case (f x); Simpl; Ground; Inversion H0; Ground.
  Rewrite <- (H a) in H1; Auto; Discriminate H1.
  Qed.

  Lemma for_all_1: 
    (s:t)(f:elt->bool)(compat_bool E.eq f) -> 
       (For_all [x](f x)=true s) -> (for_all f s)=true.
  Proof. 
  Induction s; Simpl; Auto; Unfold For_all.
  Intros x l Hrec f Hf. 
  Generalize (Hf x); Case (f x); Simpl; Ground. 
  Rewrite (H x); Auto.
  Qed.

  Lemma for_all_2: 
    (s:t)(f:elt->bool)(compat_bool E.eq f) -> (for_all f s)=true -> 
    (For_all [x](f x)=true s).
  Proof. 
  Induction s; Simpl; Auto; Unfold For_all.
  Intros; Inversion H1.
  Intros x l Hrec f Hf. 
  Intros A a; Intros. 
  Assert (f x)=true.
   Generalize A; Case (f x); Auto.
  Rewrite H0 in A; Simpl in A.
  Inversion H; Ground.
  Rewrite (Hf a x); Auto.
  Qed.

  Lemma exists_1: 
    (s:t)(f:elt->bool)(compat_bool E.eq f) -> (Exists [x](f x)=true s) -> 
    (exists f s)=true.
  Proof.
  Induction s; Simpl; Auto; Unfold Exists.
  Intros.
  Elim H0; Intuition. 
  Inversion H2.
  Intros x l Hrec f Hf. 
  Generalize (Hf x); Case (f x); Simpl; Ground. 
  Inversion_clear H0.
  Absurd (false=true); Auto with bool.
  Rewrite (H x); Auto.
  Rewrite <- H1.
  Ground.
  Ground.
  Qed.

  Lemma exists_2: 
    (s:t)(f:elt->bool)(compat_bool E.eq f) -> (exists f s)=true -> 
    (Exists [x](f x)=true s).
  Proof. 
  Induction s; Simpl; Auto; Unfold Exists.
  Intros; Discriminate.
  Intros x l Hrec f Hf.
  Generalize (refl_equal ? (f x)); Pattern -1 (f x); Case (f x). 
  Intros; Exists x; Auto.
  Intros; Elim (Hrec f); Auto; Ground.
  Qed.

  Lemma partition_Inf_1 : 
     (s:t)(Hs:(Sort s))(f:elt->bool)(x:elt)(Inf x s) -> 
     (Inf x (fst ? ? (partition f s))).
  Proof.
  Induction s; Simpl.
  Intuition.  
  Intros x l Hrec Hs f a Ha; Inversion_clear Hs; Inversion Ha.
  Generalize (Hrec H f a).
  Case (f x); Case (partition f l); Simpl.
  Intros; Constructor; Auto.
  EAuto.
  Qed.

  Lemma partition_Inf_2 : 
     (s:t)(Hs:(Sort s))(f:elt->bool)(x:elt)(Inf x s) -> 
     (Inf x (snd ? ? (partition f s))).
  Proof.
  Induction s; Simpl.
  Intuition.  
  Intros x l Hrec Hs f a Ha; Inversion_clear Hs; Inversion Ha.
  Generalize (Hrec H f a).
  Case (f x); Case (partition f l); Simpl.
  EAuto.
  Intros; Constructor; Auto.
  Qed.

  Lemma partition_sort_1 : (s:t)(Hs:(Sort s))(f:elt->bool)
    (Sort (fst ? ? (partition f s))).
  Proof.
  Induction s; Simpl.
  Auto.
  Intros x l Hrec Hs f; Inversion_clear Hs.
  Generalize (Hrec H f); Generalize (partition_Inf_1 H f).
  Case (f x); Case (partition f l); Simpl; Auto.
  Qed.
  
  Lemma partition_sort_2 : (s:t)(Hs:(Sort s))(f:elt->bool)
     (Sort (snd ? ? (partition f s))).
  Proof.
  Induction s; Simpl.
  Auto.
  Intros x l Hrec Hs f; Inversion_clear Hs.
  Generalize (Hrec H f); Generalize (partition_Inf_2 H f).
  Case (f x); Case (partition f l); Simpl; Auto.
  Qed.

  Lemma partition_1: 
    (s:t)(f:elt->bool)(compat_bool E.eq f) -> 
    (Equal (fst ? ? (partition f s)) (filter f s)).
  Proof.
  Induction s; Simpl; Auto; Unfold Equal.
  Ground.
  Intros x l Hrec f Hf.
  Generalize (Hrec f Hf); Clear Hrec.
  Case (partition f l); Intros s1 s2; Simpl; Intros.
  Case (f x); Simpl; Ground; Inversion H0;  Intros; Ground. 
  Qed.
   
  Lemma partition_2: 
    (s:t)(f:elt->bool)(compat_bool E.eq f) -> 
    (Equal (snd ? ? (partition f s)) (filter [x](negb (f x)) s)).
  Proof.
  Induction s; Simpl; Auto; Unfold Equal.
  Ground.
  Intros x l Hrec f Hf. 
  Generalize (Hrec f Hf); Clear Hrec.
  Case (partition f l); Intros s1 s2; Simpl; Intros.
  Case (f x); Simpl; Ground; Inversion H0; Intros; Ground. 
  Qed.
 
  Definition eq : t -> t -> Prop := Equal.

  Lemma eq_refl: (s:t)(eq s s). 
  Proof. 
  Unfold eq Equal; Intuition.
  Qed.

  Lemma eq_sym: (s,s':t)(eq s s') -> (eq s' s).
  Proof. 
  Unfold eq Equal; Ground.
  Qed.

  Lemma eq_trans: (s,s',s'':t)(eq s s') -> (eq s' s'') -> (eq s s'').
  Proof. 
  Unfold eq Equal; Ground.
  Qed.

  Inductive lt : t -> t -> Prop := 
     lt_nil : (x:elt)(s:t)(lt [] (x::s)) 
   | lt_cons_lt : (x,y:elt)(s,s':t)(E.lt x y) -> (lt (x::s) (y::s'))
   | lt_cons_eq :  (x,y:elt)(s,s':t)(E.eq x y) -> (lt s s') -> (lt (x::s) (y::s')).
  Hint lt := Constructors lt.
   
  Lemma lt_trans : (s,s',s'':t)(lt s s') -> (lt s' s'') -> (lt s s'').
  Proof. 
  Intros s s' s'' H; Generalize s''; Clear s''; Elim H.
  Intros x l s'' H'; Inversion_clear H'; Auto.
  Intros x x' l l' E s'' H'; Inversion_clear H'; Auto. 
  EAuto.
  Constructor 2; Apply ME.lt_eq with x'; Auto.
  Intros.
  Inversion_clear H3.
  Constructor 2; Apply ME.eq_lt with y; Auto.
  Constructor 3; EAuto.  
  Qed. 

  Lemma lt_not_eq : (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(lt s s') -> ~(eq s s').
  Proof. 
  Unfold eq Equal. 
  Intros s s' Hs Hs' H; Generalize Hs Hs'; Clear Hs Hs'; Elim H; Intros; Intro.
  Elim (H0 x); Intros.
  Assert X : (In x []); Auto; Inversion X.
  Inversion_clear Hs; Inversion_clear Hs'.
  Elim (H1 x); Intros. 
  Assert X : (In x y::s'0); Auto; Inversion_clear X.
  Absurd (E.eq x y); EAuto.
  Absurd (E.lt y x); Auto.
  EApply In_sort; EAuto.
  Inversion_clear Hs; Inversion_clear Hs'.
  Elim H2; Auto; Intuition.
  Elim (H3 a); Intros.
  Assert X: (In a y::s'0); Auto; Inversion_clear X; Auto.
  Absurd (E.lt x a); EAuto.
  EApply In_sort with s0; EAuto.
  Elim (H3 a); Intros.
  Assert X: (In a x::s0); Auto; Inversion_clear X; Auto.
  Absurd (E.lt y a); EAuto.
  EApply In_sort with s'0; EAuto.
  Qed.

  Definition compare : (s,s':t)(Hs:(Sort s))(Hs':(Sort s'))(Compare lt eq s s').
  Proof.
  Induction s.
  Intros; Case s'. 
  Constructor 2; Apply eq_refl. 
  Constructor 1; Auto.
  Intros a l Hrec s'; Case s'.
  Constructor 3; Auto.
  Intros a' l' Hs Hs'.
  Case (E.compare a a'); [ Constructor 1 | Idtac | Constructor 3 ]; Auto.
  Elim (Hrec l'); [ Constructor 1 | Constructor 2 | Constructor 3 | Inversion Hs | Inversion Hs']; Auto.
  Generalize e; Unfold eq Equal; Intuition; 
    Inversion_clear H; EAuto; Elim (e1 a0); Auto.
  Defined.

End Raw.

(** Now, in order to really provide a functor implementing S, we 
   need to encapsulate everything into a type of strictly ordered lists. *)

Module Make [X:OrderedType] <: S with Module E := X.

 Module E := X.
 Module Raw := (Raw X). 

 Record slist : Set := { this :> Raw.t ; sorted : (sort E.lt this) }.
 Definition t := slist. 
 Definition elt := X.t.
 
 Definition In := [x:elt;s:t](Raw.In x s).
 Definition Equal := [s,s'](a:elt)(In a s)<->(In a s').
 Definition Subset := [s,s'](a:elt)(In a s)->(In a s').
 Definition Add := [x:elt;s,s':t](y:elt)(In y s') <-> ((E.eq y x)\/(In y s)).
 Definition Empty := [s](a:elt)~(In a s).
 Definition For_all := [P:elt->Prop; s:t](x:elt)(In x s)->(P x).
 Definition Exists := [P:elt->Prop; s:t](EX x:elt | (In x s)/\(P x)).
  
 Definition In_1 := [s:t](!Raw.In_eq s).
 
 Definition mem := [x:elt;s:t](Raw.mem x s).
 Definition mem_1 := [s:t](Raw.mem_1 (sorted s)). 
 Definition mem_2 := [s:t](!Raw.mem_2 s).

 Definition add := [x,s](Build_slist (Raw.add_sort (sorted s) x)).
 Definition add_1 :=  [s:t](Raw.add_1 (sorted s)).
 Definition add_2 := [s:t](Raw.add_2 (sorted s)).
 Definition add_3 := [s:t](Raw.add_3 (sorted s)).

 Definition remove := [x,s](Build_slist (Raw.remove_sort (sorted s) x)).
 Definition remove_1 :=  [s:t](Raw.remove_1 (sorted s)).
 Definition remove_2 := [s:t](Raw.remove_2 (sorted s)).
 Definition remove_3 := [s:t](Raw.remove_3 (sorted s)).
 
 Definition singleton := [x](Build_slist (Raw.singleton_sort x)).
 Definition singleton_1 := Raw.singleton_1.
 Definition singleton_2 := Raw.singleton_2.
  
 Definition union := [s,s':t](Build_slist (Raw.union_sort (sorted s) (sorted s'))). 
 Definition union_1 := [s,s':t](Raw.union_1 (sorted s) (sorted s')).
 Definition union_2 := [s,s':t](Raw.union_2 (sorted s) (sorted s')).
 Definition union_3 := [s,s':t](Raw.union_3 (sorted s) (sorted s')).

 Definition inter :=[s,s':t](Build_slist (Raw.inter_sort (sorted s) (sorted s'))). 
 Definition inter_1 := [s,s':t](Raw.inter_1 (sorted s) (sorted s')).
 Definition inter_2 := [s,s':t](Raw.inter_2 (sorted s) (sorted s')).
 Definition inter_3 := [s,s':t](Raw.inter_3 (sorted s) (sorted s')).
 
 Definition diff :=[s,s':t](Build_slist (Raw.diff_sort (sorted s) (sorted s'))). 
 Definition diff_1 := [s,s':t](Raw.diff_1 (sorted s) (sorted s')).
 Definition diff_2 := [s,s':t](Raw.diff_2 (sorted s) (sorted s')).
 Definition diff_3 := [s,s':t](Raw.diff_3 (sorted s) (sorted s')).
 
 Definition equal := [s,s':t](Raw.equal s s'). 
 Definition equal_1 := [s,s':t](Raw.equal_1 (sorted s) (sorted s')).  
 Definition equal_2 := [s,s':t](!Raw.equal_2 s s').
 
 Definition subset := [s,s':t](Raw.subset s s').
 Definition subset_1 := [s,s':t](Raw.subset_1 (sorted s) (sorted s')).  
 Definition subset_2 := [s,s':t](!Raw.subset_2 s s').

 Definition empty := (Build_slist Raw.empty_sort).
 Definition empty_1 := Raw.empty_1.
 
 Definition is_empty := [s:t](Raw.is_empty s).
 Definition is_empty_1 := [s:t](!Raw.is_empty_1 s).
 Definition is_empty_2 := [s:t](!Raw.is_empty_2 s).

 Definition elements := [s:t](Raw.elements s).
 Definition elements_1 := [s:t](!Raw.elements_1 s).
 Definition elements_2 := [s:t](!Raw.elements_2 s).
 Definition elements_3 := [s:t](Raw.elements_3 (sorted s)).
 
 Definition min_elt := [s:t](Raw.min_elt s).
 Definition min_elt_1 := [s:t](!Raw.min_elt_1 s).
 Definition min_elt_2 := [s:t](Raw.min_elt_2 (sorted s)).
 Definition min_elt_3 := [s:t](!Raw.min_elt_3 s).

 Definition max_elt := [s:t](Raw.max_elt s).
 Definition max_elt_1 := [s:t](!Raw.max_elt_1 s).
 Definition max_elt_2 := [s:t](Raw.max_elt_2 (sorted s)).
 Definition max_elt_3 := [s:t](!Raw.max_elt_3 s).
  
 Definition choose := min_elt.
 Definition choose_1 := min_elt_1.
 Definition choose_2 := min_elt_3.
 
 Definition fold := [B:Set; f: elt->B->B; s:t](!Raw.fold B f s). 
 Definition fold_1 := [s:t](!Raw.fold_1 s). 
 Definition fold_2 := [s,s':t](Raw.fold_2 (sorted s) (sorted s')).
 
 Definition cardinal := [s:t](Raw.cardinal s).
 Definition cardinal_1 := [s:t](!Raw.cardinal_1 s). 
 Definition cardinal_2 := [s,s':t](Raw.cardinal_2 (sorted s) (sorted s')).
 
 Definition filter := [f: elt->bool; s:t](Build_slist (Raw.filter_sort (sorted s) f)).
 Definition filter_1 := [s:t](!Raw.filter_1 s).
 Definition filter_2 := [s:t](!Raw.filter_2 s).
 Definition filter_3 := [s:t](!Raw.filter_3 s).
 
 Definition for_all := [f:elt->bool; s:t](Raw.for_all f s).
 Definition for_all_1 := [s:t](!Raw.for_all_1 s). 
 Definition for_all_2 := [s:t](!Raw.for_all_2 s). 

 Definition exists := [f:elt->bool; s:t](Raw.exists f s).
 Definition exists_1 := [s:t](!Raw.exists_1 s). 
 Definition exists_2 := [s:t](!Raw.exists_2 s). 

 Definition partition := [f:elt->bool; s:t]
    let p = (Raw.partition f s) in  
    ((!Build_slist (fst ?? p) (Raw.partition_sort_1 (sorted s) f)), 
     (!Build_slist (snd ?? p) (Raw.partition_sort_2 (sorted s) f))).
 Definition partition_1 := [s:t](!Raw.partition_1 s).
 Definition partition_2 := [s:t](!Raw.partition_2 s). 

 Definition eq := [s,s':t](Raw.eq s s').
 Definition eq_refl := [s:t](Raw.eq_refl s).
 Definition eq_sym := [s,s':t](!Raw.eq_sym s s').
 Definition eq_trans := [s,s',s'':t](!Raw.eq_trans s s' s'').
  
 Definition lt := [s,s':t](Raw.lt s s').
 Definition lt_trans := [s,s',s'':t](!Raw.lt_trans s s' s'').
 Definition lt_not_eq := [s,s':t](Raw.lt_not_eq (sorted s) (sorted s')).

 Definition compare : (s,s':t)(Compare lt eq s s').
 Proof.
 Intros; Elim (Raw.compare (sorted s) (sorted s')); 
  [Constructor 1 | Constructor 2 | Constructor 3]; Auto. 
 Defined.

End Make.

(* TODO: functions in Raw should be all tail-recursive; 
   here is a beginning

  Fixpoint rev_append [s:t] : t -> t := Cases s of
    nil => [s']s'
  | (cons x l) => [s'](rev_append l x::s')
  end.

  Lemma rev_append_correct : (s,s':t)(rev_append s s')=(app (rev s) s').
  Proof.
  Induction s; Simpl; Auto.
  Intros.
  Rewrite H.
  Rewrite app_ass.
  Simpl; Auto.
  Qed.

  (* a tail_recursive [rev]. *)
  Definition rev_tl := [s:t](rev_append s []).

  Lemma rev_tl_correct : (s:t)(rev_tl s)=(rev s).
  Proof.
  Unfold rev_tl; Intros; Rewrite rev_append_correct; Symmetry;
    Exact (app_nil_end (rev s)).
  Qed.

  (* a tail_recursive [union] *)
  Fixpoint union_tl_aux [acc,s:t] : t -> t := Cases s of
    nil => [s'](rev_append s' acc)
  | (cons x l) =>
       (Fix union_aux { union_aux / 2 : t -> t -> t := [acc,s']Cases s' of
           nil => (rev_append s acc)
         | (cons x' l') => Cases (E.compare x x') of
              (Lt _ ) => (union_tl_aux x::acc l s')
            | (Eq _ ) => (union_tl_aux x::acc l l')
            | (Gt _) => (union_aux x'::acc l')
            end
         end} acc)
   end.

  Definition union_tl := [s,s':t](rev_tl (union_tl_aux [] s s')).

  Lemma union_tl_correct :
    (s,s':t)(union_tl s s')=(union s s').
  Proof.
  Assert  (s,s',acc:t)(union_tl_aux acc s s')=(rev_append (union s s') acc).
   Induction s.
   Simpl; Auto.
   Intros x l Hrec; Induction s'; Auto; Intros x' l' Hrec' acc.
   Simpl; Case (E.compare x x'); Simpl; Intros; Auto.
   Change (union_tl_aux x'::acc x::l l')=(rev_append (union x::l l') x'::acc); Ground.
  Unfold union_tl; Intros; Rewrite H; Auto.
  Change (rev_append (union s s') []) with (rev_tl (union s s')).
  Do 2 Rewrite rev_tl_correct.
  Exact (idempot_rev (union s s')).
  Qed.

*)

