Require Import Ltac2.Ltac2 Ltac2.Notations.

Goal True -> False.
Proof.
Fail
let b := { contents := true } in
let f c :=
  match b.(contents) with
  | true => Message.print (Message.of_constr c); b.(contents) := false; fail
  | false => ()
  end
in
(** This fails because the matching is not allowed to backtrack once
    it commits to a branch*)
lazy_match! '(nat -> bool) with context [?a] => f a end.
lazy_match! Control.goal () with ?a -> ?b => Message.print (Message.of_constr b) end.
Abort.
