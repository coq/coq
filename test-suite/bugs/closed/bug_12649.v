

Module Type A.

  Record baz : Prop := B { }. (* any sort would do *)

End A.

Print A.
Module Type UseA (c: A). End UseA.
Print UseA. (* ANOMALY! Int.Map.get's assert false *)
