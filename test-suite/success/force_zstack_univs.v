(* PRun does not carry a primitive universe instance.  In particular, a
   malformed primitive instance cannot be smuggled through Ltac2 unsafe
   construction and then hidden in a lazy-conversion stack frame. *)

Require Import Corelib.Force Ltac2.Ltac2.
Set Default Proof Mode "Classic".

Polymorphic Definition one_univ_source@{u} (A : Type@{u}) := A.
Ltac2 one_inst () :=
  match Constr.Unsafe.kind '(@one_univ_source@{Set}) with
  | Constr.Unsafe.Constant _ u => u
  | _ => Control.throw Assertion_failure
  end.

Axiom b : Blocked nat.

Goal True.
Proof.
  (* [PRun] does not take a universe instance. *)
  Fail ltac2:(
    let _ := Constr.Unsafe.PRun (one_inst ()) 'nat 'nat 'b '(fun x : nat => x) in
    ()
  ).

  exact I.
Qed.
