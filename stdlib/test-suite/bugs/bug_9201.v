From Stdlib Require Import Ring.

Set Universe Polymorphism.
Inductive word : Type -> Type :=.
Axiom wzero : forall sz, word sz.
Axiom wone : forall sz, word sz.
Axiom wplus : forall sz, word sz -> word sz -> word sz.
Axiom wmult : forall sz, word sz -> word sz -> word sz.
Axiom wminus : forall sz, word sz -> word sz -> word sz.
Axiom wneg : forall sz, word sz -> word sz.
Axiom wring : forall sz, ring_theory (wzero sz) (wone sz) (@wplus sz) (@wmult sz) (@wminus sz) (@wneg sz) (@eq _).
Local Unset Universe Polymorphism.
Section foo.
  Context (sz : Type).
  Add Ring word_sz_ring : (wring sz). (* success *)
End foo.
Local Set Universe Polymorphism.
Section foo'.
  Context (sz : Type).
  Fail Add Ring word_sz_ring' : (wring sz).
  (* Error: Cannot add a universe monomorphic declaration when section polymorphic universes are present. *)
End foo'.
