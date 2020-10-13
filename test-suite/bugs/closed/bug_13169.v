Goal False.
Proof.
  set (H1:=I).
  set (x:=true).
  assert (H2: x = true) by reflexivity.
  set (y:=false).
  assert (H3: y = false) by reflexivity.
  clearbody H1 x y.
  eenough (H4: _ = false).
  vm_compute in H4.
  (* H4 now has "x:=y" in the evar context. *)
  2: exact H3.
  match type of H4 with y = false => idtac end.
Abort.
