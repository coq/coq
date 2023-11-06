
Lemma foo (n:nat) : match n with 0 => 0 | _ => 1 end = 0.
Proof.
  set (m := match n with 0 => _ | _ => _ end).
  Validate Proof.
Abort.
