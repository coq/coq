From Stdlib Require Import Lia.
Goal forall n (B: n >= 0), exists Goal1 Goal2 Goal3,
  (0 * (Goal1 * Goal2 + Goal1) <> Goal3 * 0 * (Goal1 * S Goal2)).
Proof. eexists _, _, _. Fail lia. Abort.
