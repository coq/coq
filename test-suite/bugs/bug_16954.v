Fail Type
  match ltac:(exact_no_check (Some true)) with
  | None => None
  | Some x => Some (x+1)
  end.
(* Anomaly "Uncaught exception Reduction.NotConvertible." *)
