Theorem inj_proj : forall A B (p1 p2:A*B),
    fst p1 = fst p2 ->
    snd p1 = snd p2 ->
    p1 = p2.
Proof.
  destruct p1, p2; simpl; intros; congruence.
Qed.

Hint Resolve inj_proj.

Definition state := (nat * nat)%type.

Theorem surjective_pairing : forall (p:state) a b,
    fst p = a ->
    snd p = b ->
    p = (a, b).
Proof.
  intros.
  Fail simple apply inj_proj.
  Fail solve [ eauto ].
  Fail solve [ eauto using inj_proj ].
Abort.
