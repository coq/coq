(* Was an anomaly with ill-typed template polymorphism *)
Definition huh (b:bool) := if b then Set else Prop.
Definition lol b: huh b :=
  if b return huh b then nat else True.
Goal (lol true) * unit.
Fail generalize true. (* should fail with error, not anomaly *)
Abort.
