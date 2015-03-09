Require Import TestSuite.admit.
(* Check that eq_sym is still pointing to Logic.eq_sym after use of Function *)

Require Import ZArith.
Require Recdef.

Axiom nat_eq_dec: forall x y : nat, {x=y}+{x<>y}.

Locate eq_sym.  (* Constant Coq.Init.Logic.eq_sym  *)

Function loop (n: nat) {measure (fun x => x) n} : bool :=
  if nat_eq_dec n 0 then false else loop (pred n).
Proof.
   admit.
Defined.

Check eq_sym eq_refl : 0=0.

