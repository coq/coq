Require Export ArrayOp.
Require Export Cyclic31.

Local Open Scope int31_scope.
Local Open Scope bool_scope.

Set Vm Optimize.

Definition to_list (A:Type) (t:array A) :=
  let len := length _ t in
  if len == 0 then nil
  else foldi_down _ (fun i l => get _ t i :: l)%list (len - 1) 0 nil.

Definition forallb (A:Type) (f:A->bool) (t:array A) :=
  let len := length _ t in
  if len == 0 then true
  else
    foldi_cont31 _ _ (fun i (cont:unit -> bool) (_:unit) =>
      if f (get _ t i) then cont tt else false) 0 (length _ t - 1) 
    (fun _ => true) tt.

Definition existsb (A:Type) (f:A->bool) (t:array A) :=
  let len := length _ t in
  if len == 0 then false
  else
    foldi_cont31 _ _ (fun i (cont:unit -> bool) (_:unit) =>
         if f (get _ t i) then true else cont tt) 0 (length _ t - 1)
    (fun _ => false) tt.


