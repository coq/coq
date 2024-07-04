From Coq Require Import ssreflect.
Class Trivial := trivial {}.
#[local] Existing Instance trivial.
Goal Trivial.
  Succeed assert True.
  have: True.
Abort.
