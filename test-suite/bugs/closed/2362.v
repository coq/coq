Set Implicit Arguments.

Class Pointed (M:Type -> Type) := 
{
  creturn: forall {A: Type}, A -> M A
}.

Unset Implicit Arguments.
Inductive FPair (A B:Type) (neutral: B) : Type:=
 fpair : forall (a:A) (b:B), FPair A B neutral.
Arguments fpair {A B neutral}.

Set Implicit Arguments.

Notation "( x ,> y )" := (fpair x y) (at level 0).

Instance Pointed_FPair B neutral:
 Pointed (fun A => FPair A B neutral) :=
 { creturn := fun A (a:A) => (a,> neutral) }.
Definition blah_fail (x:bool) : FPair bool nat O :=
  creturn x.
Set Printing All. Print blah_fail.

Definition blah_explicit (x:bool) : FPair bool nat O :=
  @creturn _ (Pointed_FPair _ ) _ x.

Print blah_explicit.


Instance Pointed_FPair_mono:
 Pointed (fun A => FPair A nat 0) :=
 { creturn := fun A (a:A) => (a,> 0) }.


Definition blah (x:bool) : FPair bool nat O :=
  creturn x.


