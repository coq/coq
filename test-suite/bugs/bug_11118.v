(* cf. https://github.com/coq/coq/issues/11118 *)

From Coq Require Import ssreflect.
From Coq Require Import List.

Lemma no_rhs (A: list (nat * nat)) (f: nat -> nat) :
  map (fun (a: nat * nat) => fst (let '(x, y) := a in (f x, f y))) A = map (fun (a: nat * nat) => f (fst a)) A.
Proof.
under map_ext => a.
Fail rewrite (surjective_pairing a); over. (* No applicable tactic. *)
rewrite [in UNDER](surjective_pairing a); over.
done.
Qed.
