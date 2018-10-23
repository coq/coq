(* This used to raise an anomaly in 8.8 *)

Inductive T := Tau (t : T).

Notation idT t := (match t with Tau t => Tau t end).

Lemma match_itree : forall (t : T), t = idT t.
Proof. destruct t; auto. Qed.

Lemma what (k : unit -> T) : k tt = k tt.
Proof. rewrite match_itree. Abort.
