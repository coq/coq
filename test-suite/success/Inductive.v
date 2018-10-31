(* Test des definitions inductives imbriquees *)

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
       match e in (@eq1 A0 B0 a0) return (P A0 a0) with
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
   match a as a0 in (A _ _ _ _ y1) return (P y1 a0) with
   | I _ _ _ _ x0 => f x0
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
   | Build_B _ _ _ _ x0 x1 => f x0 x1
   end).

(* Check inductive types with local definitions (constructors) *)

Inductive I1 : Set := C1 (_:I1) (_:=0).

Check (fun x:I1 =>
  match x with
  | C1 i n => (i,n)
  end).

(* Check implicit parameters of inductive types (submitted by Pierre
  Casteran and also implicit in BZ#338) *)

Set Implicit Arguments.
Unset Strict Implicit.

CoInductive LList (A : Set) : Set :=
  | LNil : LList A
  | LCons : A -> LList A -> LList A.

Arguments LNil [A].

Inductive Finite (A : Set) : LList A -> Prop :=
  | Finite_LNil : Finite LNil
  | Finite_LCons :
      forall (a : A) (l : LList A), Finite l -> Finite (LCons a l).

(* Check positivity modulo reduction (cf bug BZ#983) *)

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

(* Test recursively non-uniform parameters (was formerly in params_ind.v) *)

Inductive list (A : Set) : Set :=
  | nil : list A
  | cons : A -> list (A -> A) -> list A.

(* Check inference of evars in arity using information from constructors *)

Inductive foo1 : forall p, Prop := cc1 : foo1 0.

(* Check cross inference of evars from constructors *)

Inductive foo2 : forall p, Prop := cc2 : forall q, foo2 q | cc3 : foo2 0.

(* An example with reduction removing an occurrence of the inductive type in one of its argument *)

Inductive IND1 (A:Type) := CONS1 : IND1 ((fun x => A) IND1).

(* These types were considered as ill-formed before March 2015, while they
   could be accepted considering that the type IND1 above was accepted *)

Inductive IND2 (A:Type) (T:=fun _ : Type->Type => A) := CONS2 : IND2 A -> IND2 (T IND2).

Inductive IND3 (A:Type) (T:=fun _ : Type->Type => A) := CONS3 : IND3 (T IND3) -> IND3 A.

Inductive IND4 (A:Type) := CONS4 : IND4 ((fun x => A) IND4) -> IND4 A.

(* This type was ok before March 2015 *)

Inductive IND5 (A : Type) (T := A) : Type := CONS5 : IND5 ((fun _ => A) 0) -> IND5 A.

(* An example of nested positivity which was rejected by the kernel
   before 24 March 2015 (even with Unset Elimination Schemes to avoid
   the _rect bug) due to the wrong computation of non-recursively
   uniform parameters in list' *)

Inductive list' (A:Type) (B:=A) :=
| nil' : list' A
| cons' : A -> list' B -> list' A.

Inductive tree := node : list' tree -> tree.

(* This type was raising an anomaly when building the _rect scheme,
   because of a bug in Inductiveops.get_arity in the presence of
   let-ins and recursively non-uniform parameters. *)

Inductive L (A:Type) (T:=A) : Type := C : L nat -> L A.

(* This type was raising an anomaly when building the _rect scheme,
   because of a wrong computation of the number of non-recursively
   uniform parameters when conversion is needed, leading the example to
   hit the Inductiveops.get_arity bug mentioned above (see #3491) *)

Inductive IND6 (A:Type) (T:=A) := CONS6 : IND6 T -> IND6 A.


Module TemplateProp.

  (** Check lowering of a template universe polymorphic inductive to Prop *)
  
  Inductive Foo (A : Type) : Type := foo : A -> Foo A.
  
  Check Foo True : Prop.

End TemplateProp.

Module PolyNoLowerProp.

  (** Check lowering of a general universe polymorphic inductive to Prop is _failing_ *)
  
  Polymorphic Inductive Foo (A : Type) : Type := foo : A -> Foo A.
  
  Fail Check Foo True : Prop.

End PolyNoLowerProp.

(* Test building of elimination scheme with noth let-ins and
   non-recursively uniform parameters *)

Module NonRecLetIn.

  Unset Implicit Arguments.

  Inductive Ind (b:=2) (a:nat) (c:=1) : Type :=
  | Base : Ind a
  | Rec : Ind (S a) -> Ind a.

  Check Ind_rect (fun n (b:Ind n) => b = b)
    (fun n => eq_refl)
    (fun n b c => f_equal (Rec n) eq_refl) 0 (Rec 0 (Base 1)).

End NonRecLetIn.

(* Test treatment of let-in in the definition of Records *)
(* Should fail with "Sort expected" *)

Fail Inductive foo (T : Type) : let T := Type in T :=
  { r : forall x : T, x = x }.
