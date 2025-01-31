
Module Type Typ.

End Typ.

Module Update_DT .
  Axiom eq_equiv : True.
End Update_DT.

Module OTF_to_TotalOrder (O:Typ).
  Include Update_DT.
End OTF_to_TotalOrder.

Module MakeRaw(X:Typ).

  Module L := OTF_to_TotalOrder X.

End MakeRaw.

Module IntMake (X: Typ) .
  Module Raw := MakeRaw  X.
End IntMake.

Include IntMake.

Module Raw2 := Raw.

Check Raw2.L.eq_equiv.
(* Error:
Anomaly
"Bad constant pair:
expected (bar.Raw2.L.eq_equiv, bar.Raw.L.eq_equiv)
but got  (bar.Raw2.L.eq_equiv, bar.Update_DT.eq_equiv)" Please report at http://coq.inria.fr/bugs/.
*)
