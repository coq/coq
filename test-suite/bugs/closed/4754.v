
Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms.
Definition f (v : option nat) := match v with
                                 | Some k => Some k
                                 | None => None
                                 end.

Axioms F G : (option nat -> option nat) -> Prop.
Axiom FG : forall f, f None = None -> F f = G f.

Axiom admit : forall {T}, T.

Existing Instance eq_Reflexive.

Global Instance foo (A := nat)
  : Proper ((pointwise_relation _ eq)
              ==> eq ==> forall_relation (fun _ => Basics.flip Basics.impl))
           (@option_rect A (fun _ => Prop)) | 0.
exact admit.
Qed.

Global Instance bar (A := nat)
  : Proper ((pointwise_relation _ eq)
              ==> eq ==> eq ==> Basics.flip Basics.impl)
           (@option_rect A (fun _ => Prop)) | 0.
exact admit.
Qed.

Goal forall k, option_rect (fun _ => Prop) (fun v : nat => v = v /\ F f) True k.
Proof.
  intro.
  pose proof (_ : (Proper (_ ==> eq ==> _) and)).
  setoid_rewrite (FG _ _); [ | reflexivity.. ].
  Undo.
  setoid_rewrite (FG _ eq_refl). (* Error: Tactic failure: setoid rewrite failed: Nothing to rewrite. in 8.5 *) Admitted.
