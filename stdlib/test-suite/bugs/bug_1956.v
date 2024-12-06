From Stdlib Require Import Program.

Inductive exp_raw : nat -> Set :=
| exp_raw_bvar : forall n i, i < n -> exp_raw n
| exp_raw_fvar : forall n, nat -> exp_raw n
| exp_raw_abs : forall n, exp_raw (S n) -> exp_raw n
| exp_raw_app : forall n, exp_raw n -> exp_raw n -> exp_raw n.

(* The following definition is not accepted. *)

Program Definition is_abs (n : nat) (e : exp_raw n) : bool :=
  match e with
    | exp_raw_abs _ _ => true
    | _ => false
   end.
