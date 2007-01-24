(* -*- coq-prog-args: ("-emacs-U" "-debug") -*- *)
Require Import JMeq.
Require Import List.
Require Import Coq.subtac.Utils.

Set Implicit Arguments.

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

Next Obligation.
  intros.
  simpl in l0.
  apply le_S_n ; exact l0.
Defined.

Next Obligation.
  intros.
  destruct_call take ; subtac_simpl.
Defined.

Next Obligation.
  intros.
  inversion l0.
Defined.




