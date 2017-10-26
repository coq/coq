Inductive boolP : Prop :=
| trueP : boolP
| falseP : boolP.

Fail Check boolP_rect.


Inductive True : Prop := I : True.

Inductive False : Prop :=.

Inductive Empty_set : Set :=.

Fail Inductive Large_set : Set :=
  large_constr : forall A : Set, A -> Large_set.

Inductive smallunitProp : Prop :=
| onlyProps : True -> smallunitProp.

Check smallunitProp_rect.

Inductive nonsmallunitProp : Prop :=
| notonlyProps : nat -> nonsmallunitProp.

Fail Check nonsmallunitProp_rect.
Set Printing Universes.
Inductive inferProp :=
| hasonlyProps : True -> nonsmallunitProp -> inferProp.

Check (inferProp : Prop).

Inductive inferSet :=
| hasaset : nat -> True -> nonsmallunitProp -> inferSet.

Fail Check (inferSet : Prop).

Check (inferSet : Set).

Inductive inferLargeSet :=
| hasalargeset : Set -> True -> nonsmallunitProp -> inferLargeSet.

Fail Check (inferLargeSet : Set).

Inductive largeProp : Prop := somelargeprop : Set -> largeProp.


Inductive comparison : Set :=
  | Eq : comparison
  | Lt : comparison
  | Gt : comparison.

Inductive CompareSpecT (Peq Plt Pgt : Prop) : comparison -> Type :=
 | CompEqT : Peq -> CompareSpecT Peq Plt Pgt Eq
 | CompLtT : Plt -> CompareSpecT Peq Plt Pgt Lt
 | CompGtT : Pgt -> CompareSpecT Peq Plt Pgt Gt.

Inductive color := Red | Black.

Inductive option (A : Type) : Type :=
| None : option A
| Some : A -> option A.
