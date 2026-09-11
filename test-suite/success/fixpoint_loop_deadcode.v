(* cf. https://github.com/rocq-prover/rocq/issues/19547 *)

Inductive Box (A : Type) : Type := box (a : A).
Inductive P : Set := PRec : P -> P.

Fixpoint rec (X : P) : False :=
  let boxP : Box P := (fix loop (p : P) : Box P := match p with PRec p' => loop p' end) X in
  match boxP with
  | box _ p => rec p
  end.
