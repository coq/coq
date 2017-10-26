Section foo.
  Context (F : Type -> Type).
  Context (admit : forall {T}, F T = True).
  Hint Rewrite (fun T => @admit T).
  Lemma bad : F False.
  Proof.
    autorewrite with core.
    constructor.
  Qed.
End foo. (* Anomaly: Universe Top.16 undefined. Please report. *)
