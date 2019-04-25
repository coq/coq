Require Import Ltac2.Ltac2.

Goal True.
Proof.
let x := Control.plus
  (fun () => let _ := constr:(nat -> 0) in 0)
  (fun e => match e with Not_found => 1 | _ => 2 end) in
match Int.equal x 2 with
| true => ()
| false => Control.throw (Tactic_failure None)
end.
Abort.
