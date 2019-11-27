(* cf. https://github.com/coq/coq/issues/11118 *)

From Coq Require Import ssreflect.
From Coq Require Import List.

Set Debug SsrMatching.

Lemma no_rhs (A: list (nat * nat)) (f: nat -> nat) :
  map (fun (a: nat * nat) => fst (let '(x, y) := a in (f x, f y))) A = map (fun (a: nat * nat) => f (fst a)) A.
Proof.
under map_ext => a.
  rewrite (surjective_pairing a).
  over. (* was failing with: No applicable tactic. *)
done.
Admitted.
