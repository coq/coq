
Definition p := 0.
Definition m := 0.

Module Test_Import.
  Module P.
    Definition p := 1.
  End P.

  Module M.
    Import P.
    Definition m := p.
  End M.

  Module N.
    Import M.

    Lemma th0 : p = 0.
      reflexivity.
    Qed.

  End N.


  (* M and P should be closed *)
  Lemma th1 : m = 0 /\ p = 0.
    split; reflexivity.
  Qed.


  Import N.

  (* M and P should still be closed *)
  Lemma th2 : m = 0 /\ p = 0.
    split; reflexivity.
  Qed.
End Test_Import.


(********************************************************************)


Module Test_Export.
  Module P.
    Definition p := 1.
  End P.

  Module M.
    Export P.
    Definition m := p.
  End M.

  Module N.
    Export M.

    Lemma th0 : p = 1.
      reflexivity.
    Qed.

  End N.


  (* M and P should be closed *)
  Lemma th1 : m = 0 /\ p = 0.
    split; reflexivity.
  Qed.


  Import N.

  (* M and P should now be opened *)
  Lemma th2 : m = 1 /\ p = 1.
    split; reflexivity.
  Qed.
End Test_Export.
