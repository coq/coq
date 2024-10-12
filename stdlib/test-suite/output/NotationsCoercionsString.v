(* Tests about skipping a coercion vs using a notation involving a coercion *)

From Stdlib Require Import String.

(* Skipping a coercion vs using a notation for the application of the
    coercion (from Robbert Krebbers, see PR #8890) *)

Module A.

Inductive expr :=
  | Var : string -> expr
  | Lam : string -> expr -> expr
  | App : expr -> expr -> expr.

Notation Let x e1 e2 := (App (Lam x e2) e1).
Parameter e1 e2 : expr.
Check (Let "x" e1 e2). (* always printed the same *)
Coercion App : expr >-> Funclass.
Check (Let "x" e1 e2). (* printed the same from #8890, in 8.10 *)
Axiom free_vars :> expr -> list string.
Check (Let "x" e1 e2) : list string. (* printed the same from #11172, in 8.12 *)

End A.
