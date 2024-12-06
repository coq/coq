Require Import Setoid Corelib.Program.Basics.
Global Open Scope program_scope.
Axiom foo : forall A (f : A -> A), f ∘ f = f.
Require Import Corelib.Program.Tactics.
#[export] Hint Rewrite foo.
Theorem t {A B C D} (f : A -> A) (g : B -> C) (h : C -> D)
: f ∘ f = f.
Proof.
  rewrite_strat topdown (hints core).
Abort.
