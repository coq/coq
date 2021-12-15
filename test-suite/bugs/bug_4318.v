(* Check no anomaly is raised *)
Fail Definition foo p := match p with (x, y) z => tt end.
