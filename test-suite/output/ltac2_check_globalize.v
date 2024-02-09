Require Import Ltac2.Ltac2.

Unset Ltac2 Typed Notations.

Ltac2 Notation "foo" := ().

Ltac2 Globalize foo.

Ltac2 Check foo.

Ltac2 Check (fun x => x : 'a -> 'a).

Ltac2 Globalize (() ()).

Ltac2 Notation "bar" := (1,2).

(* check that CTacApp nodes don't get merged or that we handle merging them correctly. *)
Ltac2 Globalize bar 3.

Ltac2 Globalize let x := () in x ().

Fail Ltac2 Check let x := () in x ().

Ltac2 Notation "complicated_typing" x(tactic) :=
  let _ := x 1 in
  let _ := x "" in
  ().

Ltac2 Globalize complicated_typing (fun x => x).

Ltac2 Check complicated_typing (fun x => x).

Ltac2 Globalize
  let accu := { contents := [] } in
  complicated_typing (fun x => accu.(contents) := x :: accu.(contents));
  accu.(contents).

Fail Ltac2 Check
  let accu := { contents := [] } in
  complicated_typing (fun x => accu.(contents) := x :: accu.(contents));
  accu.(contents).

Ltac2 Globalize lazy_match! goal with
  | [h: _ |- _] => (* lots of code... *) Std.clear h (* more code... *)
  | [|- _] => (* lots of code... *) ()
  end.

Ltac2 Globalize constr:(ltac2:(foo)).
