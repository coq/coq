Require Import Coq.Program.Wf.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Utils.
Require Import Coq.NArith.BinNat.
Require Import Psatz.
Open Scope N_scope.

Ltac solve_fib :=
  program_simplify;
  try apply N.lt_wf_0;
  repeat match goal with  H : _ = false |- _ => apply N.eqb_neq in H end;
  lia.

Program Fixpoint fib (n : N) {measure n (N.lt)} : N
 := if dec (n =? 0) then 0 else
    if n =? 1 then 1 else
    fib (n - 1) + fib (n - 2).
Solve Obligations with (solve_fib).


Goal fib 5 = 5. reflexivity. Qed.