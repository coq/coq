Require Import Program.Basics Program.Tactics.
Set Implicit Arguments.
Unset Strict Implicit.

Definition def (a : nat) := a = a.

Structure record {a : nat} {D : def a} :=
  inR { prop : Prop }.

Program
Canonical Structure ins (a : nat) (rec : @record a _) :=
  @inR a _ (prop rec).
Next Obligation.
  exact eq_refl.
Defined.
Next Obligation.
  exact eq_refl.
Defined.
