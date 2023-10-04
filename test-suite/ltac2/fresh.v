Require Import Ltac2.Ltac2.

Goal True.
Proof.
  let f := Fresh.Free.of_goal () in
  let h0 := ident:(H) in
  let h1 := Fresh.fresh f h0 in
  let f := FSet.add h1 f in
  let h2 := Fresh.fresh f h0 in
  pose0 false (fun () => Some h1, 'I);
  pose0 false (fun () => Some h2, 'I).
  Check H.
  Check H0.
Abort.
