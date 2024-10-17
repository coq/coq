Require Import BinNums PosDef PrimInt63 PrimArray.

Definition foo (n : positive) :=
  let a := make 2 0 in
  let b := Pos.iter (fun b => set b 1 1) a (xO (xO (xO (xO (xO (xI (xO (xI (xO (xI (xI (xO (xO (xO (xO (xI xH)))))))))))))))) (* 100000 *) in
  let v := get b 0 in
  Pos.iter (fun v => v + get a 0) v n.

Timeout 5 Time Eval vm_compute in foo (xO (xO (xO (xO (xO (xO (xI (xO (xO (xI (xO (xO (xO (xO (xI (xO (xI (xI (xI xH))))))))))))))))))) (* 1000000 *).
