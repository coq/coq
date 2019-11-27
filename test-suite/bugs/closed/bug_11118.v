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

(* The regression test below goes beyond reproducing the bug *)
Lemma no_rhs' (A: list (nat * nat)) (f: nat -> nat) :
  map (fun (a: nat * nat) => fst (let '(x, y) := a in (f x, f y))) A = map (fun (a: nat * nat) => f (fst a)) A.
Proof.
under map_ext => a.
  Fail rewrite [in X in @Under_rel _ _ _ X](surjective_pairing a).
  unfold ssrmatching.nomatch.
  rewrite [in X in @Under_rel _ _ _ X](surjective_pairing a).
Abort.
