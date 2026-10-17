
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

(* Reduction used to instantiate delayed recursive calls. *)
Module Reduction.

  Fixpoint beta (n : nat) : nat :=
    match n with
    | 0 => 0
    | S p => (fun q => beta q) p
    end.

  Fixpoint alias (n : nat) : nat :=
    let g := alias in
    match n with
    | 0 => 0
    | S p => g p
    end.

  (* Reject the recursive call exposed by beta reduction. *)
  Fail Fixpoint beta_same (n : nat) : nat :=
    match n with
    | 0 => 0
    | S _ => (fun q => beta_same q) n
    end.

  (* Reject an invalid call even when an enclosing let would erase it. *)
  Fail Fixpoint invalid (n : nat) : nat :=
    let _ := invalid (S n) in 0.

  (* An outer let can erase a blocked match containing a delayed call. *)
  Fixpoint blocked (b : bool) (n : nat) : nat :=
    let _ :=
      match b with
      | true => fun _ : nat => 0
      | false => blocked b
      end
    in 0.

  Unset Guard Checking Option Reduction.

  Fail Fixpoint beta_off (n : nat) : nat :=
    match n with
    | 0 => 0
    | S p => (fun q => beta_off q) p
    end.

  Fail Fixpoint alias_off (n : nat) : nat :=
    let g := alias_off in
    match n with
    | 0 => 0
    | S p => g p
    end.

  (* Ordinary recursion and weak-head subterm reduction remain available. *)
  Fixpoint direct (n : nat) : nat :=
    match n with
    | 0 => 0
    | S p => direct ((fun q => q) p)
    end.

End Reduction.
