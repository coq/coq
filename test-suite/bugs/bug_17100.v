Set Warnings "+bad-relevance".

Module Test1.

Axiom Prop1 : Prop.
Axiom Prop2 : Prop.
Axiom equiv : Prop1 <-> Prop2.

Lemma buggy (P : SProp) : Prop1 -> P -> P.
Proof.
  intros HO.
  apply equiv in HO.
  refine (fun x => x).
Qed. (* Bad relevance in case annotation. [bad-relevance,debug] *)

End Test1.

Module Test2.

Axiom Type1 : Type.
Axiom Type2 : Type.
Axiom equiv : inhabited (Type1 -> Type1).

Lemma buggy (P : Prop) : Type1 -> True.
Proof.
  intros H.
  Fail apply equiv in H.
Abort.

End Test2.

Module Test3.

Axiom In : forall [A : Type] (a : A) (l : list A), Prop.
Definition all_equiv (l: list Prop) := forall x y, In x l -> In y l -> (x <-> y).

Axiom last : forall [A : Type], list A -> A -> A.
Axiom in_eq : forall [A : Type] (a : A) (l : list A), In a (a :: l).
Axiom in_last : forall [A : Type] (a b : A) (l : list A), In (last (b :: l) a) (a :: b :: l).

(* Check that apply in handles correctly binders in the lemma *)
Goal forall (b : Prop) (l : list Prop) (a : Prop)
  (H : all_equiv (a :: b :: l)), last (b :: l) a -> a.
Proof.
intros b l a H.
apply H.
+ apply in_eq.
+ apply in_last.
Qed.

End Test3.
