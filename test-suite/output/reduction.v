(* Test the behaviour of hnf and simpl introduced in revision *)

Parameter n:nat.
Definition a:=0.

Eval simpl in (fix plus (n m : nat) {struct n} : nat :=
  match n with
  | 0 => m
  | S p => S (p + m)
  end) a a.

Eval hnf in match (plus (S n) O) with S n => n | _ => O end.

Eval simpl head in 2 + 2.
Eval cbn head in 2 + 2.
Eval lazy head in 2 + 2.
Eval cbv head in 2 + 2.

Eval lazy head delta in 2 + 2.

Eval simpl head in 2 + (2 + 2).

Eval simpl head in (2 + 2) + 2.

Eval cbv head in (2 + 2) + 2.

Axiom ignore : forall {T}, T -> unit.
Eval simpl head in ignore (fun x => 1 + x).
Eval cbn head in ignore (fun x => 1 + x).
Eval lazy head in ignore (fun x => 1 + x).
Eval cbv head in ignore (fun x => 1 + x).

Require Import Ltac2.Ltac2.

Ltac2 Eval eval lazy in (2 + 2).
Ltac2 Eval eval lazy head in (2 + 2).

(* Cbv examples *)

Eval cbv head beta delta iota in let x := 1 + 1 in 2 + 2. (* not fully clear what head w/o zeta should be *)
Eval cbv beta delta iota in let x := 1 + 1 in 2 + 2. (* not fully clear what head w/o zeta should be *)
Eval cbv head beta delta iota in (let x := 1 + 1 in fun x => 1 + x) 2. (* not fully clear whether we should apply commutative cuts or not *)
Eval cbv head in match 0 + n with 0 => 1 + 1 | S n => 1 + n end.
Eval cbv head in fix f n := match 0 + n with 0 => 1 + 1 | S n => 1 + f n end.

Require Import PrimInt63.
Eval cbv head in PrimInt63.add 2 2.
Parameter x:int.
Eval cbv head in PrimInt63.add 2 x.

Require Import PrimFloat.
Eval cbv head in 0x1p+0%float.
