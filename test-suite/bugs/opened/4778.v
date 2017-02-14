Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms.
Definition f (v : option nat) := match v with
                                 | Some k => Some k
                                 | None => None
                                 end.

Axioms F G : (option nat -> option nat) -> Prop.
Axiom FG : forall f, f None = None -> F f = G f.

Axiom admit : forall {T}, T.

Existing Instance eq_Reflexive.

(* This instance is needed in 8.4, but is useless in 8.5 *)
Global Instance foo (A := nat)
  : Proper ((pointwise_relation _ eq)
              ==> eq ==> forall_relation (fun _ => Basics.flip Basics.impl))
           (@option_rect A (fun _ => Prop)) | 0.
exact admit.
Qed.

(*
(* This is required in 8.5, but useless in 8.4 *)
Global Instance bar (A := nat)
  : Proper ((pointwise_relation _ eq)
              ==> eq ==> eq ==> Basics.flip Basics.impl)
           (@option_rect A (fun _ => Prop)) | 0.
exact admit.
Qed.
*)

Goal forall k, option_rect (fun _ => Prop) (fun v : nat => v = v /\ F f) True k. Proof.
  intro.
  pose proof (_ : (Proper (_ ==> eq ==> _) and)).
  Fail setoid_rewrite (FG _ _); [ | reflexivity.. ]. (* this should succeed without [Fail], as it does in 8.4 *)
