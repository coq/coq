Require Import List.
Require Import Arith.
Require Import Recdef.
Require Import Omega.

Function foo (xys : (list nat * list nat)) {measure (fun xys => length (fst xys) + length (snd xys))} : list nat :=
  match xys with
    | (nil, _) => snd xys
    | (_, nil) => fst xys
    | (x :: xs', y :: ys') => match Nat.compare x y with
                                | Lt => x :: foo (xs', y :: ys')
                                | Eq => x :: foo (xs', ys')
                                | Gt => y :: foo (x :: xs', ys')
                              end
  end.
Proof.
  intros; simpl; omega.
  intros; simpl; omega.
  intros; simpl; omega.
Qed.

Function bar (xys : (list nat * list nat)) {measure (fun xys => length (fst xys) + length (snd xys))} : list nat :=
  let (xs, ys) := xys in
  match (xs, ys) with
    | (nil, _) => ys
    | (_, nil) => xs
    | (x :: xs', y :: ys') => match Nat.compare x y with
                                | Lt => x :: foo (xs', ys)
                                | Eq => x :: foo (xs', ys')
                                | Gt => y :: foo (xs, ys')
                              end
  end.
