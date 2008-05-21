(* Here are a sequences of scripts to test interactively with undo and
   replay in coqide proof sessions *)

(* Undoing arbitrary commands, as first step *)

Theorem a : O=O.
Set Printing All.
assert True by trivial.
trivial.
Qed.

(* Undoing arbitrary commands, as non-first step *)

Theorem b : O=O.
assert True by trivial.
Set Printing All.
assert True by trivial.
trivial.
Qed.

(* Undoing declarations, as first step *)
(* was bugged in 8.1 *)

Theorem c : O=O.
Inductive T : Type := I.
trivial.
Qed.

(* Undoing declarations, as first step *)
(* new in 8.2 *)

Theorem d : O=O.
Definition e := O.
Definition f := O.
assert True by trivial.
trivial.
Qed.

(* Undoing declarations, as non-first step *)
(* new in 8.2 *)

Theorem h : O=O.
assert True by trivial.
Definition i := O.
Definition j := O.
assert True by trivial.
trivial.
Qed.

(* Undoing declarations, interleaved with proof steps *)
(* new in 8.2 *)

Theorem k : O=O.
assert True by trivial.
Definition l := O.
assert True by trivial.
Definition m := O.
assert True by trivial.
trivial.
Qed.

(* Undoing declarations, interleaved with proof steps and commands *)
(* new in 8.2 *)

Theorem n : O=O.
assert True by trivial.
Definition o := O.
Set Printing All.
assert True by trivial.
Focus.
Definition p := O.
assert True by trivial.
trivial.
Qed.

(* Undoing declarations, not in proof *)

Definition q := O.
Definition r := O.
