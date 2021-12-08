Require Import BinPos Uint63 PArray.

Definition foo (n : positive) :=
  let a := make 2 0 in
  let b := Pos.iter (fun b => set b 1 1) a 100000 in
  let v := get b 0 in
  Pos.iter (fun v => v + get a 0) v n.

Timeout 5 Time Eval vm_compute in foo 1000000.
