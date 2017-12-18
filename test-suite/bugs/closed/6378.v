Require Import Coq.ZArith.ZArith.
Ltac profile_constr tac :=
  let dummy := match goal with _ => reset ltac profile; start ltac profiling end in
  let ret := match goal with _ => tac () end in
  let dummy := match goal with _ => stop ltac profiling; show ltac profile end in
  pose 1.

Ltac slow _ := eval vm_compute in (Z.div_eucl, Z.div_eucl, Z.div_eucl, Z.div_eucl, Z.div_eucl).

Goal True.
  start ltac profiling.
  reset ltac profile.
  reset ltac profile.
  stop ltac profiling.
  time profile_constr slow.
  show ltac profile cutoff 0.
  show ltac profile "slow".
Abort.
