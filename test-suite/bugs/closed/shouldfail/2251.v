(* Check that rewrite does not apply to single evars *)

Lemma evar_rewrite : (forall a : nat, a = 0 -> True) -> True.
intros; eapply H.  (* goal is  ?30 = nil  *)
Fail rewrite plus_n_Sm.
Abort.
