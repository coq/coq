(* Submitted by Randy Pollack *)

Record pred [S:Set]: Type := { sp_pred :> S -> Prop }.
Record rel [S:Set]: Type := { sr_rel :> S -> S -> Prop }.

Section testSection.
Variables S: Set; P: (pred S); R: (rel S); x:S.
Check (P x).
Check (R x x).
