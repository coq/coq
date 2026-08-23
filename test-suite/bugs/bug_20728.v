(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Inductive STrue : SProp := SI.
Inductive Box (A : SProp) : A -> Set := box a : Box A a.

Symbol S: bool -> Type -> Set.

Rewrite Rule S_rew :=
  S _ (forall (a : ?A), Box STrue ?b) => Box _ (fun a => ?b).

Check fun (x : STrue) =>
  (eq_refl : S true (unit -> Box STrue x) = S false (unit -> Box STrue x)).

Definition error (x : STrue) :=
  (eq_refl : S true (unit -> Box STrue x) = S false (unit -> Box STrue x)).
