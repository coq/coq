(*I'm not sure which behavior is better.  But if the change is intentional, it should be documented (I don't think it is), and it'd be nice if there were a flag for this, or if -compat 8.4 restored the old behavior.*)

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
  Fail setoid_rewrite (FG _ _); []. (* In 8.5: Error: Tactic failure: Incorrect number of goals (expected 2 tactics); works in 8.4 *)
