Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Goal True.
  constructor.
Qed.
Goal True.
  constructor.
Qed.
Goal True.
  constructor.
Qed.
Goal True.
  constructor.
Qed.
Goal True.
  constructor.
Qed.
Goal List.repeat Z.div_eucl 5 = List.repeat Z.div_eucl 5.
  vm_compute; reflexivity.
Qed.
