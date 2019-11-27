(* see also test-suite/bugs/closed/bug_11118.v *)

From Coq Require Import ssreflect.
From Coq Require Import List.

Set Debug SsrMatching.

Lemma test1 (A: list (nat * nat)) (f: nat -> nat) :
  map (fun (a: nat * nat) => fst (let '(x, y) := a in (f x, f y))) A = map (fun (a: nat * nat) => f (fst a)) A.
Proof.
under map_ext => a.
  Fail rewrite [in X in @Under_rel _ _ _ X](surjective_pairing a).
  unfold ssrmatching.nomatch.
  rewrite [in X in @Under_rel _ _ _ X](surjective_pairing a).
Abort.

Section Test_nomatch.
Variables (P Q : Prop) (H : P = Q) (ok : Q).

Lemma test2 : ssrmatching.nomatch Prop P.
Fail rewrite H.
unfold ssrmatching.nomatch.
rewrite H.
exact ok.
Qed.

Lemma test3 : ssrmatching.nomatch (Prop -> Prop) (fun _ => P) P.
Fail rewrite {2}H.
rewrite H.
hnf.
Fail exact ok.
Abort.

End Test_nomatch.
