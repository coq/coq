
(* -------------------------------------------------------------------- *)
(*   Example to test patterns matching on dependent families            *)     (* This exemple extracted from the developement done by Nacira Chabane  *)
(* (equipe Paris 6)                                                     *)
(* -------------------------------------------------------------------- *)


Require Prelude.
Require Logic_TypeSyntax.
Require Logic_Type.


Section Orderings.
   Variable U: Type.
   
   Definition Relation :=  U -> U -> Prop.

   Variable R: Relation.
   
   Definition Reflexive : Prop :=  (x: U) (R x x).
   
   Definition Transitive : Prop :=  (x,y,z: U) (R x y) -> (R y z) -> (R x z).
   
   Definition Symmetric : Prop :=  (x,y: U) (R x y) -> (R y x).
   
   Definition Antisymmetric : Prop :=
      (x,y: U) (R x y) -> (R y x) -> x==y.
   
   Definition contains : Relation -> Relation -> Prop :=
      [R,R': Relation] (x,y: U) (R' x y) -> (R x y).
  Definition same_relation : Relation -> Relation -> Prop :=
      [R,R': Relation] (contains R R') /\ (contains R' R).
Inductive Equivalence : Prop :=
         Build_Equivalence:
           Reflexive -> Transitive -> Symmetric -> Equivalence.
   
   Inductive PER : Prop :=
         Build_PER: Symmetric -> Transitive -> PER.
   
End Orderings.

(***** Setoid  *******)

Inductive Setoid : Type 
  := Build_Setoid : (S:Type)(R:(Relation S))(Equivalence ? R) -> Setoid.

Definition elem := [A:Setoid]
                   <Type>Match A with [S:?][R:?][e:?]S end.

Grammar command command1 :=
 elem  [ "|" command0($s) "|"] -> [ <<(elem $s)>>].

Definition equal := [A:Setoid]
   <[s:Setoid](Relation |s|)>Match A with [S:?][R:?][e:?]R end.


Grammar command command1 :=
 equal   [ command0($c) "=" "%" "S" command0($c2) ] -> 
         [ <<(equal ? $c $c2)>>].


Axiom prf_equiv : (A:Setoid)(Equivalence |A| (equal A)).
Axiom prf_refl : (A:Setoid)(Reflexive |A| (equal A)).
Axiom prf_sym : (A:Setoid)(Symmetric |A| (equal A)).
Axiom prf_trans : (A:Setoid)(Transitive |A| (equal A)).

Section Maps.
Variables A,B: Setoid.

Definition Map_law := [f:|A|->|B|]
    (x,y:|A|) x =%S y -> (f x) =%S (f y).

Inductive Map : Type :=
    Build_Map : (f:|A|->|B|)(p:(Map_law f))Map.

Definition explicit_ap := [m:Map] <|A|->|B|>Match m with 
         [f:?][p:?]f end.

Axiom pres : (m:Map)(Map_law (explicit_ap m)).

Definition ext := [f,g:Map]
         (x:|A|) (explicit_ap f x) =%S (explicit_ap g x).

Axiom Equiv_map_eq : (Equivalence Map ext).

Definition Map_setoid := (Build_Setoid Map ext Equiv_map_eq).

End Maps.

Syntactic Definition ap := (explicit_ap ? ?). 

Grammar command command8 :=
  map_setoid [ command7($c1) "=>" command8($c2) ] 
                 -> [ <<(Map_setoid $c1 $c2)>>].


Definition ap2 := [A,B,C:Setoid][f:|(A=>(B=>C))|][a:|A|] (ap (ap f a)).


(*****    posint     ******)

Inductive posint : Type
        := Z : posint | Suc : posint -> posint.

Require Logic_Type.

Axiom f_equal : (A,B:Type)(f:A->B)(x,y:A) x==y -> (f x)==(f y).
Axiom eq_Suc : (n,m:posint) n==m -> (Suc n)==(Suc m).

(* The predecessor function *)

Definition pred : posint->posint
     := [n:posint](<posint>Case n of (* Z *) Z 
                            (* Suc u *) [u:posint]u end).

Axiom pred_Sucn : (m:posint) m==(pred (Suc m)).
Axiom eq_add_Suc : (n,m:posint) (Suc n)==(Suc m) -> n==m.
Axiom not_eq_Suc : (n,m:posint) ~(n==m) -> ~((Suc n)==(Suc m)).


Definition IsSuc : posint->Prop
  := [n:posint](<Prop>Case n of (* Z *) False
                          (* Suc p *) [p:posint]True end).
Definition IsZero :posint->Prop :=
	[n:posint]<Prop>Match n with 
		True
		[p:posint][H:Prop]False end.

Axiom Z_Suc : (n:posint) ~(Z==(Suc n)).
Axiom  Suc_Z: (n:posint) ~(Suc n)==Z.
Axiom n_Sucn : (n:posint) ~(n==(Suc n)).
Axiom Sucn_n : (n:posint) ~(Suc n)==n.
Axiom eqT_symt : (a,b:posint) ~(a==b)->~(b==a).


(*******  Dsetoid *****)

Definition Decidable :=[A:Type][R:(Relation A)]
		(x,y:A)(R x y) \/ ~(R x y).


Record DSetoid : Type :=
{Set_of : Setoid;
 prf_decid : (Decidable |Set_of| (equal Set_of))}.

(* example de Dsetoide d'entiers *)


Axiom eqT_equiv : (Equivalence posint (eqT posint)).
Axiom Eq_posint_deci : (Decidable posint (eqT posint)).

(* Dsetoide des posint*)

Definition Set_of_posint := (Build_Setoid posint (eqT posint) eqT_equiv).

Definition Dposint := (Build_DSetoid Set_of_posint Eq_posint_deci).



(**************************************)


(* Definition des signatures *)
(* une signature est un ensemble d'operateurs muni
 de l'arite de chaque operateur *)


Section Sig.

Record Signature :Type :=
{Sigma : DSetoid; 
 Arity : (Map (Set_of Sigma) (Set_of Dposint))}.

Variable S:Signature.



Variable Var : DSetoid.

Mutual Inductive TERM : Type :=
	  var : |(Set_of Var)|->TERM
	| oper : (op: |(Set_of (Sigma S))|) (LTERM (ap (Arity S) op)) -> TERM
with
	LTERM : posint -> Type :=
	  nil : (LTERM Z)
	| cons : TERM -> (n:posint)(LTERM n) -> (LTERM (Suc n)).



(* -------------------------------------------------------------------- *)
(*                  Examples                                            *)
(* -------------------------------------------------------------------- *)


Parameter t1,t2: TERM.

Type 
 Cases t1 t2 of 
   (var  v1) (var v2) => True

 | (oper op1 l1)  (oper op2 l2) => False
 | _ _ => False 
 end.



Parameter n2:posint.
Parameter l1, l2:(LTERM n2).

Type 
 Cases l1 l2  of
    nil            nil => True 
 |  (cons v m y)   nil => False
 |  _               _  => False
end.


Type Cases l1 l2 of
    nil              nil      => True 
 | (cons u n x)  (cons v m y) =>False
 |   _               _        => False
end.



Fixpoint equalT [t1:TERM]:TERM->Prop :=
[t2:TERM] 
 Cases t1 t2 of 
   (var  v1)        (var v2)    => True
 | (oper op1 l1)  (oper op2 l2) => False
 |  _                   _       => False 
 end

with EqListT [n1:posint;l1:(LTERM n1)]: (n2:posint)(LTERM n2)->Prop :=
[n2:posint][l2:(LTERM n2)]
 Cases l1 l2 of
    nil                 nil             => True 
 | (cons t1 n1' l1')  (cons t2 n2' l2') => False
 | _                    _               => False
end.


Reset equalT.
Reset EqListT.
(* ------------------------------------------------------------------*)
(*          Initial exemple (without patterns)                       *)
(*-------------------------------------------------------------------*)

Fixpoint equalT [t1:TERM]:TERM->Prop :=
<TERM->Prop>Case t1 of 
	(*var*) [v1:|(Set_of Var)|][t2:TERM]
		<Prop>Case t2 of
		(*var*)[v2:|(Set_of Var)|] (v1 =%S v2)
		(*oper*)[op2:|(Set_of (Sigma S))|][_:(LTERM (ap (Arity S) op2))]False
		end
	(*oper*)[op1:|(Set_of (Sigma S))|]
                [l1:(LTERM (ap (Arity S) op1))][t2:TERM]
                <Prop>Case t2 of
		(*var*)[v2:|(Set_of Var)|]False
		(*oper*)[op2:|(Set_of (Sigma S))|]
                        [l2:(LTERM (ap (Arity S) op2))]
			((op1=%S op2)/\ (EqListT (ap (Arity S) op1) l1 (ap (Arity S) op2) l2))
		end
end
with EqListT [n1:posint;l1:(LTERM n1)]: (n2:posint)(LTERM n2)->Prop :=
<[_:posint](n2:posint)(LTERM n2)->Prop>Case l1 of
	(*nil*) [n2:posint][l2:(LTERM n2)]
		<[_:posint]Prop>Case l2 of
		(*nil*)True
	 	(*cons*)[t2:TERM][n2':posint][l2':(LTERM n2')]False
	end
	(*cons*)[t1:TERM][n1':posint][l1':(LTERM n1')]
		[n2:posint][l2:(LTERM n2)]
		<[_:posint]Prop>Case l2 of
		(*nil*) False
		(*cons*)[t2:TERM][n2':posint][l2':(LTERM n2')]
			((equalT t1 t2) /\ (EqListT n1' l1' n2' l2'))
		end
end.


(* ---------------------------------------------------------------- *)
(*                Version with simple patterns                      *)
(* ---------------------------------------------------------------- *)
Reset equalT.

Fixpoint equalT [t1:TERM]:TERM->Prop :=
Cases t1 of 
  (var  v1) => [t2:TERM]
	        Cases t2 of
		     (var v2) => (v1 =%S v2)
		 | (oper op2 _) =>False
		 end
| (oper op1 l1) => [t2:TERM]
		    Cases t2 of
	              (var _) => False
                    | (oper op2 l2) => (op1=%S op2)
                      /\ (EqListT (ap (Arity S) op1) l1 (ap (Arity S) op2) l2)
		    end
end
with EqListT [n1:posint;l1:(LTERM n1)]: (n2:posint)(LTERM n2)->Prop :=
<[_:posint](n2:posint)(LTERM n2)->Prop>Cases l1 of
  nil => [n2:posint][l2:(LTERM n2)]
          Cases l2 of
              nil => True
	  | _  => False
	  end
| (cons t1 n1' l1') => [n2:posint][l2:(LTERM n2)]
		        Cases l2 of
		           nil =>False
		        | (cons t2 n2' l2') => (equalT t1 t2) 
                                                /\ (EqListT n1' l1' n2' l2')
		end
end.


Reset equalT.

Fixpoint equalT [t1:TERM]:TERM->Prop :=
Cases t1 of 
  (var  v1) => [t2:TERM]
	        Cases t2 of
		     (var v2) => (v1 =%S v2)
		 | (oper op2 _) =>False
		 end
| (oper op1 l1) => [t2:TERM]
		    Cases t2 of
	              (var _) => False
                    | (oper op2 l2) => (op1=%S op2)
                      /\ (EqListT (ap (Arity S) op1) l1 (ap (Arity S) op2) l2)
		    end
end
with EqListT [n1:posint;l1:(LTERM n1)]: (n2:posint)(LTERM n2)->Prop :=
[n2:posint][l2:(LTERM n2)]
Cases l1 of
  nil => 
          Cases l2 of
              nil => True
	  | _  => False
	  end
| (cons t1 n1' l1') =>  Cases l2 of
		           nil =>False
		        | (cons t2 n2' l2') => (equalT t1 t2) 
                                                /\ (EqListT n1' l1' n2' l2')
		end
end.

(* ---------------------------------------------------------------- *)
(*                  Version with multiple patterns                  *)
(* ---------------------------------------------------------------- *)
Reset equalT.

Fixpoint equalT [t1:TERM]:TERM->Prop :=
[t2:TERM] 
 Cases t1 t2 of 
   (var  v1)       (var v2)     => (v1 =%S v2)

 | (oper op1 l1)  (oper op2 l2) => 
     (op1=%S op2) /\ (EqListT (ap (Arity S) op1) l1 (ap (Arity S) op2) l2)

 |  _               _ => False 
 end

with EqListT [n1:posint;l1:(LTERM n1)]: (n2:posint)(LTERM n2)->Prop :=
[n2:posint][l2:(LTERM n2)]
 Cases l1 l2 of
    nil                nil              => True 
 | (cons t1 n1' l1')  (cons t2 n2' l2') => (equalT t1 t2) 
                                          /\ (EqListT n1' l1' n2'  l2')
 | _ _ => False
end.


(* ------------------------------------------------------------------ *)

End Sig.
