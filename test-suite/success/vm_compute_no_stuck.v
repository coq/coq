From Corelib Require Import PrimInt63 PrimArray PrimFloat PrimString.

(* Fixpoints, matches, and primitive operations are accepted when they
   reduce. *)
Eval vm_compute_no_stuck in 1 + 2.
Eval vm_compute_no_stuck in match true with true => 1 | false => 2 end.

Open Scope uint63_scope.
Eval vm_compute_no_stuck in PrimInt63.add 1 2.
Close Scope uint63_scope.

Open Scope array_scope.
Definition a : array nat := [| 1; 2 | 3 |].
Eval vm_compute_no_stuck in a.[0].
Eval vm_compute_no_stuck in (fun v => a.[0 <- v]).
Close Scope array_scope.

CoInductive stream := Cons : nat -> stream -> stream.
CoFixpoint zeros : stream := Cons 0 zeros.
Eval vm_compute_no_stuck in
  match zeros with Cons n _ => n end.

(* Other neutral terms, including stuck projections, are accepted. *)
Parameter opaque : nat -> nat.
Eval vm_compute_no_stuck in opaque 0.

#[projections(primitive)] Record R := { field : nat }.
Parameter r : R.
Eval vm_compute_no_stuck in field r.

(* Stuck cofixpoints and fixpoints are rejected at any readback depth. *)
Fail Eval vm_compute_no_stuck in zeros.
Fail Eval vm_compute_no_stuck in Cons 0 zeros.
Fail Eval vm_compute_no_stuck in Nat.add.
Fail Eval vm_compute_no_stuck in (fun n => Nat.add n 1).

(* Stuck matches are rejected. *)
Fail Eval vm_compute_no_stuck in
  (fun b => if b then 1 else 2).

(* Fully applied primitive operations that are stuck are rejected. *)
Open Scope uint63_scope.
Fail Eval vm_compute_no_stuck in
  (fun x : uint63 => PrimInt63.add x 1).
Close Scope uint63_scope.

Open Scope array_scope.
Fail Eval vm_compute_no_stuck in
  (fun A (t : array A) => t.[0]).
Close Scope array_scope.

Fail Eval vm_compute_no_stuck in
  (fun x : float => PrimFloat.add x x).
Fail Eval vm_compute_no_stuck in
  (fun s : PrimString.string => PrimString.length s).

(* Main use case: prevent catastrophic term explosions *)
Axiom n : nat.
Fail Timeout 1 Eval vm_compute in Nat.pow (100+n) 10.
Timeout 1 Fail Eval vm_compute_no_stuck in Nat.pow (100+n) 10.
