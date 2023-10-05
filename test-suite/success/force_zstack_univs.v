(* PRun/PUnblock no longer carry primitive universe instances.  In
   particular, malformed primitive instances cannot be smuggled through
   Ltac2 unsafe construction and then hidden in lazy-conversion stack frames. *)

Require Import Corelib.Force Ltac2.Ltac2.
Set Default Proof Mode "Classic".

Polymorphic Definition one_univ_source@{u} (A : Type@{u}) := A.
Polymorphic Definition two_univ_source@{u v} (A : Type@{u}) (B : Type@{v}) := A.

Ltac2 one_inst () :=
  match Constr.Unsafe.kind '(@one_univ_source@{Set}) with
  | Constr.Unsafe.Constant _ u => u
  | _ => Control.throw Assertion_failure
  end.

Ltac2 two_inst () :=
  match Constr.Unsafe.kind '(@two_univ_source@{Set Set}) with
  | Constr.Unsafe.Constant _ u => u
  | _ => Control.throw Assertion_failure
  end.

Axiom b : Blocked nat.

Goal True.
Proof.
  (* [PRun] and [PUnblock] do not take universe instances. *)
  Fail ltac2:(
    let _ := Constr.Unsafe.PRun (one_inst ()) 'nat 'nat 'b '(fun x : nat => x) in
    ()
  ).

  Fail ltac2:(
    let _ := Constr.Unsafe.PUnblock (two_inst ()) 'nat 'b in
    ()
  ).

  exact I.
Qed.
