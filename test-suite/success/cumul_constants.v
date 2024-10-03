Set Universe Polymorphism.
(* So that by default we only get Set <= a constraints, not Set < a *)
Set Printing Universes.

Definition relation@{*a +ra} (A : Type@{a}) : Type@{max(a,ra+1)} := A -> A -> Type@{ra}.
Definition respectful@{*a *ra *b *rb} {A : Type@{a}} {B : Type@{b}} (R : relation@{a ra} A) (S : relation@{b rb} B) : relation@{max(a,b) max(a, ra, rb)} (A -> B) :=
  fun f g => forall x y : A, R x y -> S (f x) (f y).

Definition Proper@{*a *ra} {A : Type@{a}} (R : relation@{a ra} A) (m : A) := R m m.

Section relation_irrel.
  Universes a a' ra.
  Constraint a <= a'.
  Variable A : Type@{a}.
  Variable R : relation@{a' ra} A.

  Set Debug "loop-checking-global".
  (* Set Debug "loop-checking-enforce-eq". *)
  Set Debug "ustate".
  Set Debug "univMinim".
  (* Unset Cumulativity Weak Constraints. *)
  Definition test := (R : relation@{a ra} A).
  Print Universes Subgraph (a a' ra).

  Context (m : A -> A).

  Context (p : Proper (respectful R R) m).
  Set Debug "backtrace".
  Lemma foo : { R : relation A & Proper (respectful R R) m }.
    eexists.
    apply p.
  Defined.





    Lemma proper_m@{a ra} () : Proper R m.


  Constraint b < a.
  Constraint c <= d.
  Fail Constraint d < c.
End test_loop.

Section funext.
  Universes a b c d.

  Constraint Set < a.
  Constraint b < a.
