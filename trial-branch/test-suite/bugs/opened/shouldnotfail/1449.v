Require Import Arith.

Goal 0 <= 0.
  eapply le_trans.
  setoid_rewrite mult_comm.
