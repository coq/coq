
Definition p:=O.
Definition m:=O.

Module Test_Import.
  Module P.
    Definition p:=(S O).
  End P.

  Module M.
    Import P.
    Definition m:=p.
  End M.

  Module N.
    Import M.

    Lemma th0 : p=O.
      Reflexivity.
    Qed.

  End N.


  (* M and P should be closed *)
  Lemma th1 : m=O /\ p=O.
    Split; Reflexivity.
  Qed.


  Import N.

  (* M and P should still be closed *)
  Lemma th2 : m=O /\ p=O.
    Split; Reflexivity.
  Qed.
End Test_Import.


(********************************************************************)


Module Test_Export.
  Module P.
    Definition p:=(S O).
  End P.

  Module M.
    Export P.
    Definition m:=p.
  End M.

  Module N.
    Export M.

    Lemma th0 : p=(S O).
      Reflexivity.
    Qed.

  End N.


  (* M and P should be closed *)
  Lemma th1 : m=O /\ p=O.
    Split; Reflexivity.
  Qed.


  Import N.

  (* M and P should now be opened *)
  Lemma th2 : m=(S O) /\ p=(S O).
    Split; Reflexivity.
  Qed.
End Test_Export.
