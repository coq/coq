Module A.
  Module Type T. Definition c := 0. #[global] Strategy expand [c]. End T.
  Module F (M:T). End F.
  Print F.
End A.

Module B.
  Module Type T. Definition c := 0. #[global] Transparent c. End T.
  Module F (M:T). End F.
  Print F.
End B.
