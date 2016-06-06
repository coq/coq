Notation prop_fun x y := (fun (x : Prop) => y).
Definition foo := fun (p : Prop) => p.
Definition bar := fun (_ : Prop) => O.
Print foo.
Print bar. (* Anomaly: Uncaught exception Not_found. Please report. *)
Goal True.
  pose bar.
  cbv [bar] in *. (* Anomaly: error with no safe_id attached: Uncaught exception Not_found.. Please report. *)
