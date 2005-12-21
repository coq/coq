
(* test the strength of pretyping unification *)

Require Import List.
Definition listn A n := {l : list A | length l = n}.
Definition make_ln A n (l : list A) (h : (fun l => length l = n) l) :=
  exist _ l h.
