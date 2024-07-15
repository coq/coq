From Ltac2 Require Import Ltac2.
From Stdlib Require Import BinNums PosDef IntDef.

(** * Test eval ... in / reduction tactics *)

(** The below test cases test if the notation syntax works - not the tactics as such *)

Ltac2 Eval (eval red in (1+2+3)).

Ltac2 Eval (eval hnf in (1+2+3)).

Ltac2 Eval (eval simpl in (1+2+3)).

Ltac2 Eval (eval simpl Z.add in (1+2+3)).

Ltac2 Eval (eval cbv in (1+2+3)).

Ltac2 Eval (eval cbv delta [Z.add] beta iota in (1+2+3)).

Ltac2 Eval (eval cbv delta [Z.add Pos.add] beta iota in (1+2+3)).

Ltac2 Eval (eval cbn in (1+2+3)).

Ltac2 Eval (eval cbn delta [Z.add] beta iota in (1+2+3)).

Ltac2 Eval (eval cbn delta [Z.add Pos.add] beta iota in (1+2+3)).

Ltac2 Eval (eval lazy in (1+2+3)).

Ltac2 Eval (eval lazy delta [Z.add] beta iota in (1+2+3)).

Ltac2 Eval (eval lazy delta [Z.add Pos.add] beta iota in (1+2+3)).

(* The example for [fold] in the reference manual *)

Ltac2 Eval (
  let t1 := '(~0=0) in
  let t2 := eval unfold not in $t1 in
  let t3 := eval pattern (0=0) in $t2 in
  let t4 := eval fold not in $t3 in
  [t1; t2; t3; t4]
).
