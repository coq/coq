

Set Universe Polymorphism.

Inductive and@{s|u v|} (A:Type@{s|u}) (B:Type@{s|v}) : Type@{s|max(u,v)} := conj (_:A) (_:B).

Lemma foo (A B:Prop) (x:and A B) : A.
Proof.
  destruct x.
  (* Error: <in exception printer>: Anomaly "Uncaught exception Option.IsNone."
     Please report at http://coq.inria.fr/bugs/.
     <original exception>: Uncaught exception Logic_monad.TacticFailure(_). *)

  assumption.
Qed.
