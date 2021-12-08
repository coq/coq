(* Check that uconstrs are interpreted in the ltac-substituted environment *)
(* Was a regression introduced in 4dab4fc (#7288) *)

Tactic Notation "bind" hyp(x) "in" uconstr(f) "as" ident(h) :=
   set (h := fun x => f).

Fact test : nat -> nat.
Proof.
  intros n.
  bind n in (n*n) as f.
  assert (f 0 = 0) by reflexivity.
Abort.
