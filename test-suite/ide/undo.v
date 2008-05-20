(* Here are a sequences of scripts to test interactively with undo and
   replay in coqide proof sessions *)

(* Undoing arbitrary commands, as first step *)

Theorem a:True.
Set Printing All.
assert True by trivial.
trivial.
Qed.

(* Undoing arbitrary commands, as non-first step *)

Theorem a:True.
assert True by trivial.
Set Printing All.
assert True by trivial.
trivial.
Qed.

(* Undoing declarations, as first step *)
(* was bugged in 8.1 *)

Theorem a:True.
Inductive T : Type := I.
trivial.
Qed.

(* Undoing declarations, as first step *)
(* new in 8.2 *)

Theorem a:True.
Definition b:=O.
Definition c:=O.
assert True by trivial.
trivial.
Qed.

(* Undoing declarations, as non-first step *)
(* new in 8.2 *)

Theorem a:True.
assert True by trivial.
Definition b:=O.
Definition c:=O.
assert True by trivial.
trivial.
Qed.

(* Undoing declarations, interleaved with proof steps *)
(* new in 8.2 *)

Theorem a:True.
assert True by trivial.
Definition b:=O.
assert True by trivial.
Definition c:=O.
assert True by trivial.
trivial.
Qed.

(* Undoing declarations, interleaved with proof steps and commands *)
(* new in 8.2 *)

Theorem a:True.
assert True by trivial.
Definition b:=O.
Set Printing All.
assert True by trivial.
Focus.
Definition c:=O.
assert True by trivial.
trivial.
Qed.
