(* Set Typeclasses Unique Instances *)
(** This lets typeclass search assume that instance heads are unique,
    so if one matches no other need to be tried,
    avoiding backtracking (even in unique solutions mode)
    This is on a class-by-class basis.
 *)

(* Non unique *)
Class B.
Class A.
Set Typeclasses Unique Instances.
(* Unique *)
Class D.
Class C (A : Type) := c : A.

#[export] Hint Mode C +.
Fail Definition test := c.

Unset Typeclasses Unique Instances.
#[export] Instance cN1 : B -> D -> C nat := fun _ _ => 0.
#[export] Instance cN2 : A -> D -> C nat := fun _ _ => 1.
#[export] Instance cB : B -> C bool := fun _ => true.

#[export] Instance Copt : forall A, C A -> C (option A) := fun A _ => None.

Set Typeclasses Debug.

Set Typeclasses Unique Solutions.
(** This forces typeclass resolution to fail if at least two solutions
   exist to a given set of constraints. This is a global setting.
   For constraints involving assumed unique instances, it will not fail
   if two such instances could apply, however it will fail if two different
   instances of a unique class could apply.
 *)
Succeed Definition foo (d d' : D) (b b' : B) (a' a'' : A) := c : nat.
Definition foo (d d' : D) (b b' : B) (a' : A) := c : nat.

Succeed Definition foo' (b b' : B) := _ : B.
Unset Typeclasses Unique Solutions.
Definition foo' (b b' : B) := _ : B.

Set Typeclasses Unique Solutions.
Definition foo'' (d d' : D) := _ : D.

(** Cut backtracking *)
Module BacktrackGreenCut.
  Unset Typeclasses Unique Solutions.
  Class C (A : Type) := c : A.

  Class D (A : Type) : Type := { c_of_d :: C A }.

  #[export] Instance D1 : D unit.
  Admitted.

  #[export] Instance D2 : D unit.
  Admitted.

  (** Two instances of D unit, but when searching for [C unit], no
      backtracking on the second instance should be needed except
      in dependent cases. Check by adding an unresolvable constraint.
   *)

  Parameter f : D unit -> C bool -> True.
  Fail Definition foo := f _ _.

  Fail Definition foo' := let y := _ : D unit in let x := _ : C bool in f _ x.

  Unset Typeclasses Strict Resolution.
  Class Transitive (A : Type) := { trans : True }.
  Class PreOrder (A : Type) := { preorder_trans :: Transitive A }.
  Class PartialOrder (A : Type) := { partialorder_trans :: Transitive A }.
  Class PartialOrder' (A : Type) := { partialorder_trans' :: Transitive A }.

  #[export] Instance: PreOrder nat. Admitted.
  #[export] Instance: PartialOrder nat. Admitted.

  Class NoInst (A : Type) := {}.

  Parameter foo : forall `{ T : Transitive nat } `{ NoInst (let x:=@trans _ T in nat) }, nat.

  Fail Definition bar := foo.


End BacktrackGreenCut.
