(* Expected time < 0.10s *)

(** A proof term is stored hash-consed, i.e. as a DAG, and [Print Assumptions]
    must walk it as one.  The proof below is a DAG of 22 nodes whose tree
    unfolding has more than four million, so a walk that loses the sharing --
    as one does when it first rebuilds the term to discharge it over the
    section -- takes time exponential in the size of this file.

    The [f0]..[f19] are distinct so that no two nodes of the DAG have the same
    head; a memo of the walked nodes that is only approximate still has to
    tell them apart. *)

Axiom ax : nat.

Definition f0 (a b : nat) : nat := Nat.add a b.
Definition f1 (a b : nat) : nat := Nat.add a b.
Definition f2 (a b : nat) : nat := Nat.add a b.
Definition f3 (a b : nat) : nat := Nat.add a b.
Definition f4 (a b : nat) : nat := Nat.add a b.
Definition f5 (a b : nat) : nat := Nat.add a b.
Definition f6 (a b : nat) : nat := Nat.add a b.
Definition f7 (a b : nat) : nat := Nat.add a b.
Definition f8 (a b : nat) : nat := Nat.add a b.
Definition f9 (a b : nat) : nat := Nat.add a b.
Definition f10 (a b : nat) : nat := Nat.add a b.
Definition f11 (a b : nat) : nat := Nat.add a b.
Definition f12 (a b : nat) : nat := Nat.add a b.
Definition f13 (a b : nat) : nat := Nat.add a b.
Definition f14 (a b : nat) : nat := Nat.add a b.
Definition f15 (a b : nat) : nat := Nat.add a b.
Definition f16 (a b : nat) : nat := Nat.add a b.
Definition f17 (a b : nat) : nat := Nat.add a b.
Definition f18 (a b : nat) : nat := Nat.add a b.
Definition f19 (a b : nat) : nat := Nat.add a b.

Section S.
  (* a section variable, so that the proof has to be discharged *)
  Context (u : nat).

  Lemma shared : nat.
  Proof.
    let x0 := constr:(Nat.add ax u) in
    let x1 := constr:(f0 x0 x0) in
    let x2 := constr:(f1 x1 x1) in
    let x3 := constr:(f2 x2 x2) in
    let x4 := constr:(f3 x3 x3) in
    let x5 := constr:(f4 x4 x4) in
    let x6 := constr:(f5 x5 x5) in
    let x7 := constr:(f6 x6 x6) in
    let x8 := constr:(f7 x7 x7) in
    let x9 := constr:(f8 x8 x8) in
    let x10 := constr:(f9 x9 x9) in
    let x11 := constr:(f10 x10 x10) in
    let x12 := constr:(f11 x11 x11) in
    let x13 := constr:(f12 x12 x12) in
    let x14 := constr:(f13 x13 x13) in
    let x15 := constr:(f14 x14 x14) in
    let x16 := constr:(f15 x15 x15) in
    let x17 := constr:(f16 x16 x16) in
    let x18 := constr:(f17 x17 x17) in
    let x19 := constr:(f18 x18 x18) in
    let x20 := constr:(f19 x19 x19) in
    exact x20.
  Qed.
End S.

Time Print Assumptions shared.
