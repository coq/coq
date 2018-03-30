
Set Printing Projections.

Class HostFunction := host_func : Type.

Section store.
  Context `{HostFunction}.
  Record store := { store_funcs : host_func }.
End store.

Check (fun (S:@store nat) => S.(store_funcs)).
