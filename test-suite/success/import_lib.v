Definition le_trans:=O.


Module Test_Read.     
  Module M.  
    Read Module Le.        (* Reading without importing *)

    Check Le.le_trans.

    Lemma th0 : le_trans = O.
      Reflexivity.
    Qed.
  End M.

  Check Le.le_trans. 

  Lemma th0 : le_trans = O.
    Reflexivity.
  Qed.

  Import M.

  Lemma th1 : le_trans = O.
    Reflexivity.
  Qed.
End Test_Read.


(****************************************************************)

Definition le_decide := (S O).  (* from Arith/Compare *)
Definition min := O.            (* from Arith/Min *)

Module Test_Require.
  
  Module M.
    Require Compare.              (* Imports Min as well *)
  
    Lemma th1 : le_decide = Compare.le_decide.
      Reflexivity.
    Qed.
  
    Lemma th2 : min = Min.min.
      Reflexivity.
    Qed.
  
  End M.
  
  (* Checks that Compare and List are loaded *)
  Check Compare.le_decide.
  Check Min.min.
  
  
  (* Checks that Compare and List are _not_ imported *)
  Lemma th1 : le_decide = (S O).
    Reflexivity.
  Qed.
  
  Lemma th2 : min = O.
    Reflexivity.
  Qed.
  
  (* It should still be the case after Import M *)
  Import M.
  
  Lemma th3 : le_decide = (S O).
    Reflexivity.
  Qed.
  
  Lemma th4 : min = O.
    Reflexivity.
  Qed.

End Test_Require.  

(****************************************************************)

Module Test_Import.
  Module M.
    Import Compare.              (* Imports Min as well *)
  
    Lemma th1 : le_decide = Compare.le_decide.
      Reflexivity.
    Qed.
  
    Lemma th2 : min = Min.min.
      Reflexivity.
    Qed.
  
  End M.
  
  (* Checks that Compare and List are loaded *)
  Check Compare.le_decide.
  Check Min.min.
  
  
  (* Checks that Compare and List are _not_ imported *)
  Lemma th1 : le_decide = (S O).
    Reflexivity.
  Qed.
  
  Lemma th2 : min = O.
    Reflexivity.
  Qed.
  
  (* It should still be the case after Import M *)
  Import M.
  
  Lemma th3 : le_decide = (S O).
    Reflexivity.
  Qed.
  
  Lemma th4 : min = O.
    Reflexivity.
  Qed.
End Test_Import.

(************************************************************************)

Module Test_Export.
  Module M.
    Export Compare.              (* Exports Min as well *)

    Lemma th1 : le_decide = Compare.le_decide.
      Reflexivity.
    Qed.

    Lemma th2 : min = Min.min.
      Reflexivity.
    Qed.

  End M.


  (* Checks that Compare and List are _not_ imported *)
  Lemma th1 : le_decide = (S O).
    Reflexivity.
  Qed.

  Lemma th2 : min = O.
    Reflexivity.
  Qed.


  (* After Import M they should be imported as well *)

  Import M.

  Lemma th3 : le_decide = Compare.le_decide.
    Reflexivity.
  Qed.

  Lemma th4 : min = Min.min.
    Reflexivity.
  Qed.
End Test_Export.


(************************************************************************)

Module Test_Require_Export.

  Definition mult_sym:=(S O).    (* from Arith/Mult *)
  Definition plus_sym:=O.        (* from Arith/Plus *)

  Module M.
    Require Export Mult.         (* Exports Plus as well *)

    Lemma th1 : mult_sym = Mult.mult_sym.
      Reflexivity.
    Qed.

    Lemma th2 : plus_sym = Plus.plus_sym.
      Reflexivity.
    Qed.

  End M.


  (* Checks that Mult and Plus are _not_ imported *)
  Lemma th1 : mult_sym = (S O).
    Reflexivity.
  Qed.

  Lemma th2 : plus_sym = O.
    Reflexivity.
  Qed.


  (* After Import M they should be imported as well *)

  Import M.

  Lemma th3 : mult_sym = Mult.mult_sym.
    Reflexivity.
  Qed.

  Lemma th4 : plus_sym = Plus.plus_sym.
    Reflexivity.
  Qed.

End Test_Require_Export.
