(* Check cast setting scopes *)
Check nat * nat : Type.
Check 0 * 0 : nat.
Require Import ZArith.
Check 0 * 0 : Z.
