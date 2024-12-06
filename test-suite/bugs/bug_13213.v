From Corelib Require Import ssreflect.
Theorem bad : True.
Proof.
  Fail abstract: True. (* could also be anything, e.g. False *)
Abort.
