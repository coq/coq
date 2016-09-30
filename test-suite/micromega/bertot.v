(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.



Goal (forall x y n,
  ( ~ x < n /\ x <= n /\ 2 * y = x*(x+1) -> 2 * y = n*(n+1))
  /\
  (x < n /\ x <= n /\ 2 * y = x * (x+1) -> x + 1 <= n /\ 2 *(x+1+y) = (x+1)*(x+2))).
Proof.
  intros.
  psatz Z 3.
Qed.

