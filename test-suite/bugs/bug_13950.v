

Record r := mk_r { x : unit }.
Definition f y := Eval vm_compute in y.(x).
Definition g y := Eval native_compute in y.(x).
