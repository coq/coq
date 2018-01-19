(* Interaction between coercions and casts *)
(*   Example provided by Eduardo Gimenez   *)

Parameter Z S : Set.

Parameter f : S -> Z.
Coercion f : S >-> Z.

Parameter g : Z -> Z.

Check (fun s => g (s:S)).


(* Check uniform inheritance condition *)

Parameter h : nat -> nat -> Prop.
Parameter i : forall n m : nat, h n m -> nat.
Coercion i : h >-> nat.

(* Check coercion to funclass when the source occurs in the target *)

Parameter C : nat -> nat -> nat.
Coercion C : nat >-> Funclass.

(* Remark: in the following example, it cannot be decided whether C is
   from nat to Funclass or from A to nat. An explicit Coercion command is
   expected

Parameter A : nat -> Prop.
Parameter C:> forall n:nat, A n -> nat.
*)

(* Check coercion between products based on eta-expansion *)
(* (there was a de Bruijn bug until rev 9254) *)

Section P.

Variable E : Set.
Variables C D : E -> Prop.
Variable G :> forall x, C x -> D x.

Check fun (H : forall y:E, y = y -> C y) => (H : forall y:E, y = y -> D y).

End P.

(* Check that class arguments are computed the same when looking for a
   coercion and when applying it (class_args_of) (failed until rev 9255) *)

Section Q.

Variable bool : Set.
Variables C D : bool -> Prop.
Variable G :> forall x, C x -> D x.
Variable f : nat -> bool.

Definition For_all (P : nat -> Prop) := forall x, P x.

Check fun (H : For_all (fun x => C (f x))) => H : forall x, D (f x).
Check fun (H : For_all (fun x => C (f x))) x => H x : D (f x).
Check fun (H : For_all (fun x => C (f x))) => H : For_all (fun x => D (f x)).

End Q.

(* Combining class lookup and path lookup so that if a lookup fails, another
   descent in the class can be found (see wish #1934) *)

Record Setoid : Type :=
{ car :>  Type }.

Record Morphism (X Y:Setoid) : Type :=
{evalMorphism :> X -> Y}.

Definition extSetoid (X Y:Setoid) : Setoid.
constructor.
exact (Morphism X Y).
Defined.

Definition ClaimA := forall (X Y:Setoid) (f: extSetoid X Y) x, f x= f x.

Coercion irrelevent := (fun _ => I) : True -> car (Build_Setoid True).

Definition ClaimB := forall (X Y:Setoid) (f: extSetoid X Y) (x:X), f x= f x.

(* Check that coercions are made visible only when modules are imported *)

Module A.
  Module B. Coercion b2n (b:bool) := if b then 0 else 1. End B.
  Fail Check S true.
End A.
Import A.
Fail Check S true.

(* Tests after the inheritance condition constraint is relaxed *)

Inductive list (A : Type) : Type := 
  nil : list A | cons : A -> list A -> list A.
Inductive vect (A : Type) : nat -> Type :=
  vnil : vect A 0 | vcons : forall n, A -> vect A n -> vect A (1+n).
Fixpoint size A (l : list A) : nat := match l with nil _ => 0 | cons _ _ tl => 1+size _ tl end.

Section test_non_unif_but_complete.
Fixpoint l2v A (l : list A) : vect A (size A l) :=
  match l as l return vect A (size A l) with
  | nil _ => vnil A
  | cons _ x xs => vcons A (size A xs) x (l2v A xs)
  end.

Local Coercion l2v : list >-> vect.
Check (fun l : list nat =>  (l : vect _ _)).

End test_non_unif_but_complete.

Section what_we_could_do.
Variables T1 T2 : Type.
Variable c12 : T1 -> T2.

Class coercion (A B : Type) : Type := cast : A -> B.
Instance atom : coercion T1 T2 := c12.
Instance pair A B C D (c1 : coercion A B) (c2 : coercion C D) : coercion (A * C) (B * D) :=
  fun x => (c1 (fst x), c2 (snd x)).

Fixpoint l2v2 {A B} {c : coercion A B} (l : list A) : (vect B (size A l)) := 
  match l as l return vect B (size A l) with
  | nil _ => vnil B
  | cons _ x xs => vcons _ _ (c x) (l2v2 xs) end.

Local Coercion l2v2 : list >-> vect.

(* This shows that there is still something to do to take full profit
   of coercions *)
Fail Check (fun l : list (T1 * T1) => (l : vect _ _)).
Check (fun l : list (T1 * T1) => (l2v2 l : vect _ _)).
End what_we_could_do.


(** Unit test for Prop as source class *)

Module TestPropAsSourceCoercion.

  Parameter heap : Prop.

  Parameter heap_empty : heap.

  Definition hprop := heap -> Prop.

  Coercion hpure (P:Prop) : hprop := fun h => h = heap_empty /\ P.

  Parameter heap_single : nat -> nat -> hprop.

  Parameter hstar : hprop -> hprop -> hprop.

  Notation "H1 \* H2" := (hstar H1 H2) (at level 69).

  Definition test := heap_single 4 5 \* (5 <> 4) \* heap_single 2 4 \* (True).

  (* Print test. -- reveals [hpure] coercions *)

End TestPropAsSourceCoercion.


(** Unit test for Type as source class *)

Module TestTypeAsSourceCoercion.

  Require Import Coq.Setoids.Setoid.

  Record setoid := { A : Type ; R : relation A ; eqv : Equivalence R }.

  Definition default_setoid (T : Type) : setoid
    := {| A := T ; R := eq ; eqv := _ |}.

  Coercion default_setoid : Sortclass >-> setoid.

  Definition foo := Type : setoid.

  Inductive type := U | Nat.
  Inductive term : type -> Type :=
  | ty (_ : Type) : term U
  | nv (_ : nat) : term Nat.

  Coercion ty : Sortclass >-> term.

  Definition ty1 := Type : term _.
  Definition ty2 := Prop : term _.
  Definition ty3 := Set : term _.
  Definition ty4 := (Type : Type) : term _.

End TestTypeAsSourceCoercion.
