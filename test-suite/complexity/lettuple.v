(* This example checks if printing nested let-in's stays in linear time *)
(* Expected time < 1.00s *)

Definition f (x : nat * nat) :=
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  let (a,b) := x in
  0.

Timeout 5 Time Print f.
