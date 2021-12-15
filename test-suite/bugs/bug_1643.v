(* Check some aspects of that the algorithm used to possibly reuse a
   global name in the recursive calls (coinductive case) *)

CoInductive Str : Set := Cons (h:nat) (t:Str).

Definition decomp_func (s:Str) :=
  match s with
    | Cons h t => Cons h t
  end.

Theorem decomp s: s = decomp_func s.
Proof.
  case s; simpl; reflexivity.
Qed.

Definition zeros := (cofix z : Str := Cons 0 z).
Lemma zeros_rw : zeros = Cons 0 zeros.
  rewrite (decomp zeros).
  simpl.
Admitted.
