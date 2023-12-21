(* Testing the behavior of implicit arguments *)

(* Implicit on section variables *)

Set Implicit Arguments.
Unset Strict Implicit.

(* Example submitted by David Nowak *)

Section Spec.
Variable A : Set.
Variable op : forall A : Set, A -> A -> Set.
Infix "#" := op (at level 70).
Check (forall x : A, x # x).

(* Example submitted by Christine *)

Record stack : Type :=
  {type : Set; elt : type; empty : type -> bool; proof : empty elt = true}.

Check
  (forall (type : Set) (elt : type) (empty : type -> bool),
   empty elt = true -> stack).

(* Nested sections and manual/automatic implicit arguments *)

Variable op' : forall A : Set, A -> A -> Set.
Variable op'' : forall A : Set, A -> A -> Set.

Section B.

Definition eq1 := fun (A:Type) (x y:A) => x=y.
Definition eq2 := fun (A:Type) (x y:A) => x=y.
Definition eq3 := fun (A:Type) (x y:A) => x=y.

Arguments op' : clear implicits.
Global Arguments op'' : clear implicits.

Arguments eq2 : clear implicits.
Global Arguments eq3 : clear implicits.

Check (op 0 0).
Check (op' nat 0 0).
Check (op'' nat 0 0).
Check (eq1 0 0).
Check (eq2 nat 0 0).
Check (eq3 nat 0 0).

End B.

Check (op 0 0).
Check (op' 0 0).
Check (op'' nat 0 0).
Check (eq1 0 0).
Check (eq2 0 0).
Check (eq3 nat 0 0).

End Spec.

Check (eq1 0 0).
Check (eq2 0 0).
Check (eq3 nat 0 0).

(* Example submitted by Frédéric (interesting in v8 syntax) *)

Parameter f : nat -> nat * nat.
Notation lhs := fst.
Check (fun x => fst (f x)).
Check (fun x => fst (f x)).
Notation rhs := snd.
Check (fun x => snd (f x)).
Check (fun x => @ rhs _ _ (f x)).

(* Implicit arguments in fixpoints and inductive declarations *)

Fixpoint g n := match n with O => true | S n => g n end.

Inductive P n : nat -> Prop := c : P n n.

(* Avoid evars in the computation of implicit arguments (cf r9827) *)

Fixpoint plus n m {struct n} :=
  match n with
  | 0 => m
  | S p => S (plus p m)
  end.

(* Check multiple implicit arguments signatures *)

Arguments eq_refl {A x}, {A}.

Check eq_refl : 0 = 0.

(* Check that notations preserve implicit (since 8.3) *)

Parameter p : forall A, A -> forall n, n = 0 -> True.
Arguments p [A] _ [n].
Notation Q := (p 0).
Check Q eq_refl.

(* Check implicits with Context *)

Section C.
Context {A:Set}.
Definition h (a:A) := a.
End C.
Check h 0.

(* Check implicit arguments in arity of inductive types. The three
   following examples used to fail before r13671 *)

Inductive I {A} (a:A) : forall {n:nat}, Prop :=
 | C : I a (n:=0).

Inductive I' [A] (a:A) : forall [n:nat], n =0 -> Prop :=
 | C' : I' a eq_refl.

Inductive I2 (x:=0) : Prop :=
 | C2 {p:nat} : p = 0 -> I2
 | C2' [p:nat] : p = 0 -> I2.
Check C2' eq_refl.

Inductive I3 {A} (x:=0) (a:A) : forall {n:nat}, Prop :=
 | C3 : I3 a (n:=0).

(* Check global implicit declaration over ref not in section *)

Section D. Global Arguments eq [A] _ _. End D.

(* Check local manual implicit arguments *)
(* Gives a warning and make the second x anonymous *)
(* Isn't the name "arg_1" a bit fragile though? *)

Check fun f : forall {x:nat} {x:bool} (x:unit), unit => f (x:=1) (arg_2:=true) tt.

(* Check the existence of a shadowing warning *)

Set Warnings "+syntax".
Fail Check fun f : forall {x:nat} {x:bool} (x:unit), unit => f (x:=1) (arg_2:=true) tt.
Set Warnings "syntax".

(* Test failure when implicit arguments are mentioned in subterms
   which are not types of variables *)

Set Warnings "+syntax".
Fail Check (id (forall {a}, a)).
Set Warnings "syntax".

(* Miscellaneous tests *)

Check let f := fun {x:nat} y => y=true in f false.
Check let f := fun [x:nat] y => y=true in f false.

(* Isn't the name "arg_1" a bit fragile, here? *)

Check fun f : forall {_:nat}, nat => f (arg_1:=0).

(* This test was wrongly warning/failing at some time *)

Set Warnings "+syntax".
Check id (fun x => let f c {a} (b:a=a) := b in f true (eq_refl 0)).
Set Warnings "syntax".


Axiom eq0le0 : forall (n : nat) (x : n = 0), n <= 0.
Parameter eq0le0' : forall (n : nat) {x : n = 0}, n <= 0.
Axiom eq0le0'' : forall (n : nat) {x : n = 0}, n <= 0.
Definition eq0le0''' : forall (n : nat) {x : n = 0}, n <= 0. Admitted.
Fail Axiom eq0le0'''' : forall [n : nat] {x : n = 0}, n <= 0.

Module TestUnnamedImplicit.

Axiom foo : forall A, A -> A.

Arguments foo {A} {_}.
Check foo (arg_2:=true) : bool.
Check foo (1:=true) : bool.
Check foo : bool.

Arguments foo {A} {x}.
Check foo (x:=true) : bool.

Axiom bar : forall A, A -> nat -> forall B, B -> A * B.
Arguments bar {A} {x} _ {B} {y}.
Check bar (1:=true) 0 (3:=false).

End TestUnnamedImplicit.

Module NotationAppliedConstantMultipleImplicit.

Axiom f : nat -> nat -> nat -> nat.
Arguments f {_} _ _, {_ _} _.
Notation "#" := (@f 0).
Check # 0 : nat.

End NotationAppliedConstantMultipleImplicit.
