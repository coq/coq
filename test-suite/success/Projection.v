Record foo (A : Type) := { B :> Type }.

Lemma bar (f : foo nat) (x : f) : x = x.
  destruct f. simpl B. simpl B in x.
Abort.

Structure S : Type :=  {Dom : Type; Op : Dom -> Dom -> Dom}.

Check (fun s : S => Dom s).
Check (fun s : S => Op s).
Check (fun (s : S) (a b : Dom s) => Op s a b).

(* v8
Check fun s:S => s.(Dom).
Check fun s:S => s.(Op).
Check fun (s:S) (a b:s.(Dom)) => s.(Op) a b.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Strict Implicit.

Structure S' (A : Set) : Type :=  {Dom' : Type; Op' : A -> Dom' -> Dom'}.

Check (fun s : S' nat => Dom' s).
Check (fun s : S' nat => Op' (s:=s)).
Check (fun s : S' nat => Op' (A:=nat) (s:=s)).
Check (fun (s : S' nat) (a : nat) (b : Dom' s) => Op' a b).
Check (fun (s : S' nat) (a : nat) (b : Dom' s) => Op' (A:=nat) (s:=s) a b).

(* v8
Check fun s:S' => s.(Dom').
Check fun s:S' => s.(Op').
Check fun (s:S') (a b:s.(Dom')) => _.(Op') a b.
Check fun (s:S') (a b:s.(Dom')) => s.(Op') a b.

Set Implicit Arguments.
Unset Strict Implicits.

Structure S' (A:Set) : Type :=
 {Dom'     : Type;
  Op'      : A -> Dom' -> Dom'}.

Check fun s:S' nat => s.(Dom').
Check fun s:S' nat => s.(Op').
Check fun (s:S' nat) (a:nat) (b:s.(Dom')) => _.(@Op' nat) a b.
Check fun (s:S' nat) (a:nat) (b:s.(Dom')) => s.(Op') a b.
*)
