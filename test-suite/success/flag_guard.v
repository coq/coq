
(* Traversing Subterm Analysis *)

Module Subterm.

  Unset Guard Checking Option Traversing Subterm Analysis.

  (* Rec call on variables are still allowed *)
  Inductive lnat :=
  | lO : lnat
  | lS : lnat -> lnat.

  Fixpoint zero (n : lnat) : lnat :=
    match n with
    | lO => lO
    | lS x => zero x
    end.

  (* Same for Primtive Projections  *)
  Set Primitive Projections.

  Inductive RNat := {
    Rb : bool;
    RNatS : Rb = true -> RNat
  }.

  Fixpoint toNat (x : RNat) : nat :=
    match x.(Rb) as y return x.(Rb) = y -> nat with
    | false => fun e => 0
    | true => fun e => S (toNat (x.(RNatS) e))
    end eq_refl.

  (* subterm analysis going through fixpoint and match are now rejected *)
  Fail Fixpoint foo n k {struct n} : nat :=
    match n with
    | 0 => 0
    | S m => foo (m - k) k
    end.

  (* Whd is still on though *)
  Fixpoint id (n : nat) : nat :=
    match n with
    | 0 => 0
    | S n => S (id ((fun x => x) n))
    end.

  (* [Unset Guard Checking] Keep the Options as is *)
  Unset Guard Checking.
  Set Guard Checking.
  Fail Fixpoint foo n k {struct n} : nat :=
    match n with
    | 0 => 0
    | S m => foo (m - k) k
    end.

  (* Accepted if the analysis is activated *)
  Set Guard Checking Option Traversing Subterm Analysis.

  Fixpoint foo n k {struct n} : nat :=
    match n with
    | 0 => 0
    | S m => foo (m - k) k
    end.

End Subterm.


(* Propagation through beta-iota cuts, independently of subterm traversal. *)
Module BetaIotaCut.

  (* Exercise recursive-call checking with an argument passed into a match. *)
  Fixpoint cut (b : bool) (n : nat) {struct n} : nat :=
    match n with
    | 0 => 0
    | S p => (match b with
              | true => fun q => cut b q
              | false => fun _ => 0
              end) p
    end.

  (* Exercise subterm analysis with a computed recursive argument. *)
  Definition select (b : bool) (p : nat) :=
    (match b with true => fun q => q | false => fun q => q end) p.

  Fixpoint computed_cut (b : bool) (n : nat) {struct n} : nat :=
    match n with
    | 0 => 0
    | S p => computed_cut b (select b p)
    end.

  Unset Guard Checking Option Beta Iota Cut.

  Fail Fixpoint cut_off (b : bool) (n : nat) {struct n} : nat :=
    match n with
    | 0 => 0
    | S p => (match b with
              | true => fun q => cut_off b q
              | false => fun _ => 0
              end) p
    end.

  Fail Fixpoint computed_cut_off (b : bool) (n : nat) {struct n} : nat :=
    match n with
    | 0 => 0
    | S p => computed_cut_off b (select b p)
    end.

End BetaIotaCut.
