
(* Print Typing Flags. *)
#[type_in_type, assume_guarded] Fixpoint f' (n : nat) : nat := f' n.

#[assume_guarded, local] Fixpoint f (n : nat) : nat.
Proof.
  exact (f n).
(* Print Typing Flags. *)
Defined.

(* Print Typing Flags. *)

Unset Universes Checking.

(* Print Tables. *)
(* Test Universes Checking. *)

Definition T := Type.
Fixpoint g (n : nat) : T := T.

(* Print Typing Flags. *)
Set Universes Checking.

#[type_in_type] Fixpoint g1 (n : nat) : T.
Proof.
  (* Print Typing Flags. *)
  exact T.
Defined.
Set Universes Checking.

Fail Definition g2 (n : nat) : T := T.
#[type_in_type] Definition g2 (n : nat) : T := T.
(* Print Typing Flags. *)

Unset Guard Checking.
Fail #[check_guarded] Definition e := fix e (n : nat) : nat := e n.
Definition e := fix e (n : nat) : nat := e n.
Set Guard Checking.

Unset Positivity Checking.
Inductive Cor :=
| Over : Cor
| Next : ((Cor -> list nat) -> list nat) -> Cor.
Set Positivity Checking.
(* Print Typing Flags. *)
(* Print Assumptions Cor. *)



#[check_universes, assume_guarded] Definition e2 : nat -> nat.
Proof.
  exact (fix e (n : nat) : nat := e n).
Defined.
(* Print Typing Flags. *)
Section b.
  Unset Universes Checking.
  Variable T : let t := Type in (t : t).
  Definition T' := T.
  (* Print Assumptions T'. *)
  (* Print Typing Flags. *)
End b.
(* Print Typing Flags. *)
Set Universes Checking.
(* Print Assumptions T'. *)

(* Unset Universes Checking. *)
#[type_in_type] Inductive T4  := a : let t := Type in (t : t) -> T4.
Module b.
  Unset Guard Checking.
  Global Unset Universes Checking.
  (* Disable Type In Type. *)
  Definition T := let t := Type in (t : t).
  (* Print Typing Flags. *)
End b.
(* Print Typing Flags. *)
Import b.
(* Print Typing Flags. *)
(* About T. *)
(* Print Assumptions T. *)
