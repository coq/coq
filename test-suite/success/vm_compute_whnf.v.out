From Corelib Require Import PrimInt63 PrimArray.

Parameter n : nat.
Parameter b : bool.
Parameter opaque : nat -> nat.

(* Computations that expose an outer value are accepted. *)
Eval vm_compute_whnf in 1 + 2.

(* Ordinary neutral heads are weak head normal forms. *)
Eval vm_compute_whnf in opaque n.

#[projections(primitive)] Record R := { field : nat }.
Parameter r : R.
Eval vm_compute_whnf in field r.

(* Only the outermost term is checked. *)
Eval vm_compute_whnf in (fun x => Nat.add x 1).
Eval vm_compute_whnf in (fun x : bool => if x then 1 else 2).

CoInductive stream := Cons : nat -> stream -> stream.
CoFixpoint zeros : stream := Cons 0 zeros.
Eval vm_compute_whnf in Cons 0 zeros.

Open Scope uint63_scope.
Parameter i : PrimInt63.int.
Eval vm_compute_whnf in (PrimInt63.add i 1, tt).
Eval vm_compute_whnf in @PrimInt63.add.
Close Scope uint63_scope.

Eval vm_compute_whnf in @PrimArray.get.

(* Outermost stuck recursive definitions and matches are rejected. *)
Fail Eval vm_compute_whnf in Nat.add.
Fail Eval vm_compute_whnf in Nat.add n 1.
Fail Eval vm_compute_whnf in zeros.
Fail Eval vm_compute_whnf in if b then 1 else 2.

(* Outermost fully applied stuck primitive operations are rejected. *)
Open Scope uint63_scope.
Fail Eval vm_compute_whnf in PrimInt63.add i 1.
Close Scope uint63_scope.

Open Scope array_scope.
Parameter a : array nat.
Fail Eval vm_compute_whnf in a.[0].
Close Scope array_scope.
