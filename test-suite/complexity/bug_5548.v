Axiom f: nat -> Type.

(* Expected time < 1.00s *)
Goal forall o, let n := 10*10*10*8 in f n ->
  o = Some tt -> o = None -> False.
Proof.
  cbv.
  Time congruence.
Qed.
