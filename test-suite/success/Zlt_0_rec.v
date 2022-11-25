Require Import ZArith Wf_Z. Local Open Scope Z_scope.
Goal True.
  let x := open_constr:(
    Zlt_0_rec
      (fun _ => Z)
      (fun x rec Hx =>
        if Z.eqb x 0
        then 0
        else 1 + rec (x-1) _)
      2 _) in
  let y := eval vm_compute in x in
  constr_eq y 2.
Abort.
