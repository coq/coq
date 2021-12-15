(* Fixing missing test for variable shadowing *)

Definition test (x y:bool*bool) :=
  match x with
  | (e as e1, (true) as e2)
  | ((true) as e1, e as e2) =>
    let '(e, b) := y in
    e
  | _ => true
  end.

Goal test (true,false) (true,true) = true.
(* used to evaluate to "false = true" in 8.4 *)
reflexivity.
Qed.
