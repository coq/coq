(* Check that the presence of binders with type annotation do not
   prevent the recursive binder part to be found *)

From Coq Require Import Utf8.

Delimit Scope C_scope with C.
Global Open Scope C_scope.

Delimit Scope uPred_scope with I.

Definition FORALL {T : Type} (f : T → Prop) : Prop := ∀ x, f x.

Notation "∀ x .. y , P" :=
  (FORALL (λ x, .. (FORALL (λ y, P)) ..)%I)
  (at level 200, x binder, y binder, right associativity) : uPred_scope.
Infix "∧" := and : uPred_scope.

(* The next command fails with
   In recursive notation with binders, Φ is expected to come without type.
   I would expect this notation to work fine, since the ∀ does support
   type annotation.
*)
Notation "'{{{' P } } } e {{{ x .. y ; pat , Q } } }" :=
  (∀ Φ : _ → _,
      (∀ x, .. (∀ y, Q ∧ Φ pat) .. ))%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  {{{ x .. y ;  pat ,  Q } } }") : uPred_scope.
