(* coq bug 5372: https://coq.inria.fr/bugs/show_bug.cgi?id=5372 *)
Require Import FunInd.
Function odd (n:nat) :=
  match n with
  | 0 => false
  | S n => true
  end
with even (n:nat) := false.
