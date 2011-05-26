(* Test des definitions inductives imbriquees *)

Require Import List.

Inductive X : Set :=
    cons1 : list X -> X.

Inductive Y : Set :=
    cons2 : list (Y * Y) -> Y.

(* Test inductive types with local definitions (arity) *)

Inductive eq1 : forall A:Type, let B:=A in A -> Prop :=
  refl1 : eq1 True I.

Check
 fun (P : forall A : Type, let B := A in A -> Type) (f : P True I) (A : Type) =>
   let B := A in
     fun (a : A) (e : eq1 A a) =>
       match e in (eq1 A0 B0 a0) return (P A0 a0) with
       | refl1 => f
       end.

Inductive eq2 (A:Type) (a:A)
  : forall B C:Type, let D:=(A*B*C)%type in D -> Prop :=
  refl2 : eq2 A a unit bool (a,tt,true).

(* Check inductive types with local definitions (parameters) *)

Inductive A (C D : Prop) (E:=C) (F:=D) (x y : E -> F) : E -> Set :=
    I : forall z : E, A C D x y z.

Check
  (fun C D : Prop =>
   let E := C in
   let F := D in
   fun (x y : E -> F) (P : forall c : C, A C D x y c -> Type)
     (f : forall z : C, P z (I C D x y z)) (y0 : C)
     (a : A C D x y y0) =>
   match a as a0 in (A _ _ _ _ _ _ y1) return (P y1 a0) with
   | I x0 => f x0
   end).

Record B (C D : Set) (E:=C) (F:=D) (x y : E -> F) : Set :=  {p : C; q : E}.

Check
  (fun C D : Set =>
   let E := C in
   let F := D in
   fun (x y : E -> F) (P : B C D x y -> Type)
     (f : forall p0 q0 : C, P (Build_B C D x y p0 q0))
     (b : B C D x y) =>
   match b as b0 return (P b0) with
   | Build_B x0 x1 => f x0 x1
   end).

(* Check inductive types with local definitions (constructors) *)

Inductive I1 : Set := C1 (_:I1) (_:=0).

Check (fun x:I1 =>
  match x with
  | C1 i n => (i,n)
  end).

(* Check implicit parameters of inductive types (submitted by Pierre
  Casteran and also implicit in #338) *)

Set Implicit Arguments.
Unset Strict Implicit.

CoInductive LList (A : Set) : Set :=
  | LNil : LList A
  | LCons : A -> LList A -> LList A.

Implicit Arguments LNil [A].

Inductive Finite (A : Set) : LList A -> Prop :=
  | Finite_LNil : Finite LNil
  | Finite_LCons :
      forall (a : A) (l : LList A), Finite l -> Finite (LCons a l).

(* Check positivity modulo reduction (cf bug #983) *)

Record P:Type := {PA:Set; PB:Set}.

Definition F (p:P) := (PA p) -> (PB p).

Inductive I_F:Set := c : (F (Build_P nat I_F)) -> I_F.

(* Check that test for binders capturing implicit arguments is not stronger
   than needed (problem raised by Cedric Auger) *)

Set Implicit Arguments.
Inductive bool_comp2 (b: bool): bool -> Prop :=
| Opp2: forall q, (match b return Prop with
                  | true => match q return Prop with 
                              true => False |
                              false => True end
                  | false => match q return Prop with
                              true => True |
                              false => False end end) -> bool_comp2 b q.

(* This one is still to be made acceptable...

Set Implicit Arguments.
Inductive I A : A->Prop := C a : (forall A, A) -> I a.

 *)
