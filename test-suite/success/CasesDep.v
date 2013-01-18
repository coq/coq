(* Check forward dependencies *)

Check
  (fun (P : nat -> Prop) Q (A : P 0 -> Q) (B : forall n : nat, P (S n) -> Q)
     x =>
   match x return Q with
   | exist _ O H => A H
   | exist _ (S n) H => B n H
   end).

(* Check dependencies in anonymous arguments (from FTA/listn.v) *)

Inductive listn (A : Set) : nat -> Set :=
  | niln : listn A 0
  | consn : forall (a : A) (n : nat), listn A n -> listn A (S n).

Section Folding.
Variable B C : Set.
Variable g : B -> C -> C.
Variable c : C.

Fixpoint foldrn (n : nat) (bs : listn B n) {struct bs} : C :=
  match bs with
  | niln _ => c
  | consn _ b _ tl => g b (foldrn _ tl)
  end.
End Folding.

(** Testing post-processing of nested dependencies *)

Check fun x:{x|x=0}*nat+nat => match x with
      | inl ((exist _ 0 eq_refl),0) => None
      | _ => Some 0
      end.

Check fun x:{_:{x|x=0}|True}+nat => match x with
      | inl (exist _ (exist _ 0 eq_refl) I) => None
      | _ => Some 0
      end.

Check fun x:{_:{x|x=0}|True}+nat => match x with
      | inl (exist _ (exist _ 0 eq_refl) I) => None
      | _ => Some 0
      end.

Check fun x:{_:{x|x=0}|True}+nat => match x return option nat with
      | inl (exist _ (exist _ 0 eq_refl) I) => None
      | _ => Some 0
      end.

  (* the next two examples were failing from r14703 (Nov 22 2011) to r14732 *)
  (* due to a bug in dependencies postprocessing (revealed by CoLoR) *)

Check fun x:{x:nat*nat|fst x = 0 & True} => match x return option nat with
      | exist2 _ _ (x,y) eq_refl I => None
      end.

Check fun x:{_:{x:nat*nat|fst x = 0 & True}|True}+nat => match x return option nat with
      | inl (exist _ (exist2 _ _ (x,y) eq_refl I) I) => None
      | _ => Some 0
      end.

(* -------------------------------------------------------------------- *)
(*   Example to test patterns matching on dependent families            *)
(* This exemple extracted from the developement done by Nacira Chabane  *)
(* (equipe Paris 6)                                                     *)
(* -------------------------------------------------------------------- *)


Require Import Prelude.
Require Import Logic_Type.

Section Orderings.
   Variable U : Type.

   Definition Relation := U -> U -> Prop.

   Variable R : Relation.

   Definition Reflexive : Prop := forall x : U, R x x.

   Definition Transitive : Prop := forall x y z : U, R x y -> R y z -> R x z.

   Definition Symmetric : Prop := forall x y : U, R x y -> R y x.

   Definition Antisymmetric : Prop := forall x y : U, R x y -> R y x -> x = y.

   Definition contains (R R' : Relation) : Prop :=
     forall x y : U, R' x y -> R x y.
  Definition same_relation (R R' : Relation) : Prop :=
    contains R R' /\ contains R' R.
Inductive Equivalence : Prop :=
    Build_Equivalence : Reflexive -> Transitive -> Symmetric -> Equivalence.

   Inductive PER : Prop :=
       Build_PER : Symmetric -> Transitive -> PER.

End Orderings.

(***** Setoid  *******)

Inductive Setoid : Type :=
    Build_Setoid :
      forall (S : Type) (R : Relation S), Equivalence _ R -> Setoid.

Definition elem (A : Setoid) := let (S, R, e) := A in S.

Definition equal (A : Setoid) :=
  let (S, R, e) as s return (Relation (elem s)) := A in R.


Axiom prf_equiv : forall A : Setoid, Equivalence (elem A) (equal A).
Axiom prf_refl : forall A : Setoid, Reflexive (elem A) (equal A).
Axiom prf_sym : forall A : Setoid, Symmetric (elem A) (equal A).
Axiom prf_trans : forall A : Setoid, Transitive (elem A) (equal A).

Section Maps.
Variable A B : Setoid.

Definition Map_law (f : elem A -> elem B) :=
  forall x y : elem A, equal _ x y -> equal _ (f x) (f y).

Inductive Map : Type :=
    Build_Map : forall (f : elem A -> elem B) (p : Map_law f), Map.

Definition explicit_ap (m : Map) :=
  match m return (elem A -> elem B) with
  | Build_Map f p => f
  end.

Axiom pres : forall m : Map, Map_law (explicit_ap m).

Definition ext (f g : Map) :=
  forall x : elem A, equal _ (explicit_ap f x) (explicit_ap g x).

Axiom Equiv_map_eq : Equivalence Map ext.

Definition Map_setoid := Build_Setoid Map ext Equiv_map_eq.

End Maps.

Notation ap := (explicit_ap _ _).

(* <Warning> : Grammar is replaced by Notation *)


Definition ap2 (A B C : Setoid) (f : elem (Map_setoid A (Map_setoid B C)))
  (a : elem A) := ap (ap f a).


(*****    posint     ******)

Inductive posint : Type :=
  | Z : posint
  | Suc : posint -> posint.

Axiom
  f_equal : forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y.
Axiom eq_Suc : forall n m : posint, n = m -> Suc n = Suc m.

(* The predecessor function *)

Definition pred (n : posint) : posint :=
  match n return posint with
  | Z => (* Z *)  Z
      (* Suc u *)
  | Suc u => u
  end.

Axiom pred_Sucn : forall m : posint, m = pred (Suc m).
Axiom eq_add_Suc : forall n m : posint, Suc n = Suc m -> n = m.
Axiom not_eq_Suc : forall n m : posint, n <> m -> Suc n <> Suc m.


Definition IsSuc (n : posint) : Prop :=
  match n return Prop with
  | Z => (* Z *)  False
      (* Suc p *)
  | Suc p => True
  end.
Definition IsZero (n : posint) : Prop :=
  match n with
  | Z => True
  | Suc _ => False
  end.

Axiom Z_Suc : forall n : posint, Z <> Suc n.
Axiom Suc_Z : forall n : posint, Suc n <> Z.
Axiom n_Sucn : forall n : posint, n <> Suc n.
Axiom Sucn_n : forall n : posint, Suc n <> n.
Axiom eqT_symt : forall a b : posint, a <> b -> b <> a.


(*******  Dsetoid *****)

Definition Decidable (A : Type) (R : Relation A) :=
  forall x y : A, R x y \/ ~ R x y.


Record DSetoid : Type :=
  {Set_of : Setoid; prf_decid : Decidable (elem Set_of) (equal Set_of)}.

(* example de Dsetoide d'entiers *)


Axiom eqT_equiv : Equivalence posint (eq (A:=posint)).
Axiom Eq_posint_deci : Decidable posint (eq (A:=posint)).

(* Dsetoide des posint*)

Definition Set_of_posint := Build_Setoid posint (eq (A:=posint)) eqT_equiv.

Definition Dposint := Build_DSetoid Set_of_posint Eq_posint_deci.



(**************************************)


(* Definition des signatures *)
(* une signature est un ensemble d'operateurs muni
 de l'arite de chaque operateur *)


Module Sig.

Record Signature : Type :=
  {Sigma : DSetoid; Arity : Map (Set_of Sigma) (Set_of Dposint)}.

Variable S : Signature.



Variable Var : DSetoid.

Inductive TERM : Type :=
  | var : elem (Set_of Var) -> TERM
  | oper :
      forall op : elem (Set_of (Sigma S)), LTERM (ap (Arity S) op) -> TERM
with LTERM : posint -> Type :=
  | nil : LTERM Z
  | cons : TERM -> forall n : posint, LTERM n -> LTERM (Suc n).



(* -------------------------------------------------------------------- *)
(*                  Examples                                            *)
(* -------------------------------------------------------------------- *)


Parameter t1 t2 : TERM.

Type
  match t1, t2 with
  | var v1, var v2 => True
  | oper op1 l1, oper op2 l2 => False
  | _, _ => False
  end.



Parameter n2 : posint.
Parameter l1 l2 : LTERM n2.

Type
  match l1, l2 with
  | nil, nil => True
  | cons v m y, nil => False
  | _, _ => False
  end.


Type
  match l1, l2 with
  | nil, nil => True
  | cons u n x, cons v m y => False
  | _, _ => False
  end.

Module Type Version1.

Definition equalT (t1 t2 : TERM) : Prop :=
  match t1, t2 with
  | var v1, var v2 => True
  | oper op1 l1, oper op2 l2 => False
  | _, _ => False
  end.

Definition EqListT (n1 : posint) (l1 : LTERM n1) (n2 : posint)
  (l2 : LTERM n2) : Prop :=
  match l1, l2 with
  | nil, nil => True
  | cons t1 n1' l1', cons t2 n2' l2' => False
  | _, _ => False
  end.

End Version1.


(* ------------------------------------------------------------------*)
(*          Initial exemple (without patterns)                       *)
(*-------------------------------------------------------------------*)

Module Version2.

Fixpoint equalT (t1 : TERM) : TERM -> Prop :=
  match t1 return (TERM -> Prop) with
  | var v1 =>
      (*var*)
      fun t2 : TERM =>
      match t2 return Prop with
      | var v2 =>
          (*var*) equal _ v1 v2
          (*oper*)
      | oper op2 _ => False
      end
      (*oper*)
  | oper op1 l1 =>
      fun t2 : TERM =>
      match t2 return Prop with
      | var v2 =>
          (*var*) False
          (*oper*)
      | oper op2 l2 =>
          equal _ op1 op2 /\
          EqListT (ap (Arity S) op1) l1 (ap (Arity S) op2) l2
      end
  end

 with EqListT (n1 : posint) (l1 : LTERM n1) {struct l1} :
 forall n2 : posint, LTERM n2 -> Prop :=
  match l1 in (LTERM _) return (forall n2 : posint, LTERM n2 -> Prop) with
  | nil =>
      (*nil*)
      fun (n2 : posint) (l2 : LTERM n2) =>
      match l2 in (LTERM _) return Prop with
      | nil =>
          (*nil*) True
          (*cons*)
      | cons t2 n2' l2' => False
      end
      (*cons*)
  | cons t1 n1' l1' =>
      fun (n2 : posint) (l2 : LTERM n2) =>
      match l2 in (LTERM _) return Prop with
      | nil =>
          (*nil*)  False
          (*cons*)
      | cons t2 n2' l2' => equalT t1 t2 /\ EqListT n1' l1' n2' l2'
      end
  end.

End Version2.

(* ---------------------------------------------------------------- *)
(*                Version with simple patterns                      *)
(* ---------------------------------------------------------------- *)

Module Version3.

Fixpoint equalT (t1 : TERM) : TERM -> Prop :=
  match t1 with
  | var v1 =>
      fun t2 : TERM =>
      match t2 with
      | var v2 => equal _ v1 v2
      | oper op2 _ => False
      end
  | oper op1 l1 =>
      fun t2 : TERM =>
      match t2 with
      | var _ => False
      | oper op2 l2 =>
          equal _ op1 op2 /\
          EqListT (ap (Arity S) op1) l1 (ap (Arity S) op2) l2
      end
  end

 with EqListT (n1 : posint) (l1 : LTERM n1) {struct l1} :
 forall n2 : posint, LTERM n2 -> Prop :=
  match l1 return (forall n2 : posint, LTERM n2 -> Prop) with
  | nil =>
      fun (n2 : posint) (l2 : LTERM n2) =>
      match l2 with
      | nil => True
      | _ => False
      end
  | cons t1 n1' l1' =>
      fun (n2 : posint) (l2 : LTERM n2) =>
      match l2 with
      | nil => False
      | cons t2 n2' l2' => equalT t1 t2 /\ EqListT n1' l1' n2' l2'
      end
  end.

End Version3.

Module Version4.

Fixpoint equalT (t1 : TERM) : TERM -> Prop :=
  match t1 with
  | var v1 =>
      fun t2 : TERM =>
      match t2 with
      | var v2 => equal _ v1 v2
      | oper op2 _ => False
      end
  | oper op1 l1 =>
      fun t2 : TERM =>
      match t2 with
      | var _ => False
      | oper op2 l2 =>
          equal _ op1 op2 /\
          EqListT (ap (Arity S) op1) l1 (ap (Arity S) op2) l2
      end
  end

 with EqListT (n1 : posint) (l1 : LTERM n1) (n2 : posint)
 (l2 : LTERM n2) {struct l1} : Prop :=
  match l1 with
  | nil => match l2 with
           | nil => True
           | _ => False
           end
  | cons t1 n1' l1' =>
      match l2 with
      | nil => False
      | cons t2 n2' l2' => equalT t1 t2 /\ EqListT n1' l1' n2' l2'
      end
  end.

End Version4.

(* ---------------------------------------------------------------- *)
(*                  Version with multiple patterns                  *)
(* ---------------------------------------------------------------- *)

Module Version5.

Fixpoint equalT (t1 t2 : TERM) {struct t1} : Prop :=
  match t1, t2 with
  | var v1, var v2 => equal _ v1 v2
  | oper op1 l1, oper op2 l2 =>
      equal _ op1 op2 /\ EqListT (ap (Arity S) op1) l1 (ap (Arity S) op2) l2
  | _, _ => False
  end

 with EqListT (n1 : posint) (l1 : LTERM n1) (n2 : posint)
 (l2 : LTERM n2) {struct l1} : Prop :=
  match l1, l2 with
  | nil, nil => True
  | cons t1 n1' l1', cons t2 n2' l2' =>
      equalT t1 t2 /\ EqListT n1' l1' n2' l2'
  | _, _ => False
  end.

End Version5.

(* ------------------------------------------------------------------ *)

End Sig.

(* Exemple soumis par Bruno *)

Definition bProp (b : bool) : Prop := if b then True else False.

Definition f0 (F : False) (ty : bool) : bProp ty :=
  match ty as _, ty return (bProp ty) with
  | true, true => I
  | _, false => F
  | _, true => I
  end.

(* Simplification of bug/wish #1671 *)

Inductive I : unit -> Type :=
| C : forall a, I a -> I tt.

(*
Definition F (l:I tt) : l = l :=
match l return l = l with
| C tt (C _ l')  => refl_equal (C tt (C _ l'))
end.

one would expect that the compilation of F (this involves
some kind of pattern-unification) would produce:
*)

Definition F (l:I tt) : l = l :=
match l return l = l with
| C tt l' => match l' return C _ l' = C _ l' with C _ l''  => refl_equal (C tt (C _ l'')) end
end.

Inductive J : nat -> Type :=
| D : forall a, J (S a) -> J a.

(*
Definition G (l:J O) : l = l :=
match l return l = l with
| D O (D 1 l')  => refl_equal (D O (D 1 l'))
| D _ _  => refl_equal _
end.

one would expect that the compilation of G (this involves inversion)
would produce:
*)

Definition G (l:J O) : l = l :=
match l return l = l with
| D 0 l'' =>
    match l'' as _l'' in J n return
      match n return forall l:J n, Prop with
      | O => fun _ => l = l
      | S p => fun l'' => D p l'' = D p l''
      end _l'' with
    | D 1 l'  => refl_equal (D O (D 1 l'))
    | _ => refl_equal _
    end
| _ => refl_equal _
end.

Fixpoint app {A} {n m} (v : listn A n) (w : listn A m) : listn A (n + m) :=
  match v with
    | niln _ => w
    | consn _ a n' v' => consn _ a _ (app v' w)
  end.

(* Testing regression of bug 2106 *)

Set Implicit Arguments.
Require Import List.

Inductive nt := E.
Definition root := E.
Inductive ctor : list nt -> nt -> Type :=
 Plus : ctor (cons E (cons E nil)) E.

Inductive term : nt -> Type :=
| Term : forall s n, ctor s n -> spine s -> term n
with spine : list nt -> Type :=
| EmptySpine : spine nil
| ConsSpine : forall n s, term n -> spine s -> spine (n :: s).

Inductive step : nt -> nt -> Type :=
  | Step : forall l n r n' (c:ctor (l++n::r) n'), spine l -> spine r -> step n
n'.

Definition test (s:step E E) :=
  match s with
    | @Step nil _ (cons E nil) _ Plus l l' => true
    | _ => false
  end.

(* Testing regression of bug 2454 ("get" used not be type-checkable when
   defined with its type constraint) *)

Inductive K : nat -> Type := KC : forall (p q:nat), K p.

Definition get : K O -> nat := fun x => match x with KC p q => q end.

(* Checking correct order of substitution of realargs *)
(* (was broken from revision 14664 to 14669) *)
(* Example extracted from contrib CoLoR *)

Inductive EQ : nat -> nat -> Prop := R x y : EQ x y.

Check fun e t (d1 d2:EQ e t) =>
      match d1 in EQ e1 t1, d2 in EQ e2 t2 return
        (e1,t1) = (e2,t2) -> (e1,t1) = (e,t) -> 0=0
      with
      | R _ _, R _ _ => fun _ _ => eq_refl
      end.
