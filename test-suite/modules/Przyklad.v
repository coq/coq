Definition ifte := [T:Set][A:Prop][B:Prop][s:(sumbool A B)][th:T][el:T] 
	   	   if s then [_]th else [_]el.

Implicits ifte.

Lemma Reflexivity_provable : 
  (A:Set)(a:A)(s:{a=a}+{~a=a})(EXT x| s==(left ? ? x)).
Intros.
Elim s.
Intro x.
Split with x; Reflexivity.

Intro.
Absurd a=a; Auto.

Save.

Lemma Disequality_provable : 
  (A:Set)(a,b:A)(~a=b)->(s:{a=b}+{~a=b})(EXT x| s==(right ? ? x)).
Intros.
Elim s.
Intro.
Absurd a=a; Auto.

Intro.
Split with b0; Reflexivity.

Save.

Module Type ELEM.
  Parameter T : Set.
  Parameter eq_dec : (a,a':T){a=a'}+{~ a=a'}.
End ELEM.
                                        
Module Type SET[Elt : ELEM].
  Parameter T : Set.
  Parameter empty : T.
  Parameter add : Elt.T -> T -> T.
  Parameter find : Elt.T -> T -> bool.

  (* Axioms *)

  Axiom find_empty_false : 
      (e:Elt.T) (find e empty) = false.

  Axiom find_add_true : 
        (s:T) (e:Elt.T) (find e (add e s)) = true.

  Axiom find_add_false :
        (s:T) (e:Elt.T) (e':Elt.T) ~(e=e') -> 
	(find e (add e' s))=(find e s).

End SET.

Module FuncDict[E : ELEM].
  Definition T := E.T -> bool.
  Definition empty := [e':E.T] false.
  Definition find := [e':E.T] [s:T] (s e').
  Definition add := [e:E.T][s:T][e':E.T]
        (ifte (E.eq_dec e e') true (find e' s)).

  Lemma find_empty_false : (e:E.T) (find e empty) = false.
    Auto.
  Qed.

  Lemma find_add_true : 
        (s:T) (e:E.T) (find e (add e s)) = true.

    Intros.
    Unfold find add.
    Elim (Reflexivity_provable ? ? (E.eq_dec e e)).
    Intros.
    Rewrite H.
    Auto.

  Qed.

  Lemma find_add_false :
        (s:T) (e:E.T) (e':E.T) ~(e=e') -> 
	(find e (add e' s))=(find e s).
    Intros.
    Unfold add find.
    Cut (EXT x:? | (E.eq_dec e' e)==(right ? ? x)).
    Intros.
    Elim H0.
    Intros.
    Rewrite H1.
    Unfold ifte.
    Reflexivity.

    Apply Disequality_provable.
    Auto.

  Qed.

End FuncDict.

Module F : SET := FuncDict.


Module Nat.
  Definition T:=nat.
  Lemma eq_dec :  (a,a':T){a=a'}+{~ a=a'}.
    Decide Equality.
  Qed.
End Nat.


Module SetNat:=F Nat. 


Lemma no_zero_in_empty:(SetNat.find O SetNat.empty)=false. 
Apply SetNat.find_empty_false. 
Save.

(***************************************************************************)
Module Lemmas[G:SET][E:ELEM].

  Module ESet:=G E.

  Lemma commute : (S:ESet.T)(a1,a2:E.T) 
    let S1 = (ESet.add a1 (ESet.add a2 S)) in 
    let S2 = (ESet.add a2 (ESet.add a1 S)) in
      (a:E.T)(ESet.find a S1)=(ESet.find a S2). 
  
    Intros.
    Unfold S1 S2.
    Elim (E.eq_dec a a1); Elim (E.eq_dec a a2); Intros H1 H2;
    Try Rewrite <- H1; Try Rewrite <- H2;
    Repeat 
      (Try (Rewrite ESet.find_add_true; Auto);
       Try (Rewrite ESet.find_add_false; Auto); 
       Auto).
  Save.
End Lemmas.


Inductive list [A:Set] : Set := nil : (list A) 
                             | cons : A -> (list A) -> (list A).

Module ListDict[E : ELEM]. 
  Definition T := (list E.T).
  Definition elt := E.T.
   
  Definition empty := (nil elt).
  Definition add := [e:elt][s:T] (cons elt e s).
  Fixpoint find [e:elt; s:T] : bool :=
        Cases s of 
          nil => false
        | (cons e' s') => (ifte (E.eq_dec e e') 
                                true
                                (find e s'))
        end.

  Definition find_empty_false := [e:elt] (refl_equal bool false).

  Lemma find_add_true : 
        (s:T) (e:E.T) (find e (add e s)) = true.
    Intros.
    Simpl.
    Elim (Reflexivity_provable ? ? (E.eq_dec e e)).
    Intros.
    Rewrite H.
    Auto.

  Qed.
  

  Lemma find_add_false :
        (s:T) (e:E.T) (e':E.T) ~(e=e') -> 
	(find e (add e' s))=(find e s).
    Intros.
    Simpl.
    Elim (Disequality_provable ? ? ? H (E.eq_dec e e')).
    Intros.
    Rewrite H0.
    Simpl.
    Reflexivity.
  Save.    
  

End ListDict.


Module L : SET := ListDict.








