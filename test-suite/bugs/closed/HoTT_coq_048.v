(** This is not the issue of https://github.com/HoTT/coq/issues/48, but was mentioned there. *)
Record Foo :=
  {
    foo := 1;
    bar : foo = foo
  }.
(* Anomaly: lookup_projection: constant is not a projection. Please report. *)
