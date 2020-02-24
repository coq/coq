Module M.

  Definition a := 0.
  Definition b := 1.

  Module N.

    Notation c := (a + b).

  End N.

End M.

Module Simple.

  Import M(a).

  Check a.
  Fail Check b.
  Fail Check N.c.

  (* todo output test: this prints a+M.b since the notation isn't imported *)
  Check M.N.c.

  Fail Import M(c).
  Fail Import M(M.b).

  Import M(N.c).
  Check N.c.
  (* interestingly prints N.c (also does with unfiltered Import M) *)

End Simple.

Module WithExport.

  Module X.
    Export M(a, N.c).
  End X.

  Import X.
  Check a.
  Check N.c. (* also prints N.c *)
  Fail Check b.

End WithExport.
