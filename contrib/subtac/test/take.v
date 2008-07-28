(* -*- coq-prog-args: ("-emacs-U" "-debug") -*- *)
Require Import JMeq.
Require Import List.
Require Import Program.

Set Implicit Arguments.
Obligations Tactic := idtac.

Print cons.

Program Fixpoint take (A : Set) (l : list A) (n : nat | n <= length l) { struct l } : { l' : list A | length l' = n } :=
  match n with
  | 0 => nil
  | S p => 
    match l with
    | cons hd tl => let rest := take tl p in cons hd rest
    | nil => !
    end
  end.

Require Import Omega.
Solve All Obligations.
Next Obligation.
  destruct_call take ; program_simpl.
Defined.

Next Obligation.
  intros.
  inversion H.
Defined.




