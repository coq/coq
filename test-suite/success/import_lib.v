Definition le_trans := 0.


Module Test_Read.
  Module M.
    Require Le.        (* Reading without importing *)

    Check Le.le_trans.

    Lemma th0 : le_trans = 0.
      reflexivity.
    Qed.
  End M.

  Check Le.le_trans.

  Lemma th0 : le_trans = 0.
    reflexivity.
  Qed.

  Import M.

  Lemma th1 : le_trans = 0.
    reflexivity.
  Qed.
End Test_Read.


(****************************************************************)

Definition le_decide := 1.  (* from Arith/Compare *)
Definition min := 0.            (* from Arith/Min *)

Module Test_Require.

  Module M.
    Require Import Compare.              (* Imports Min as well *)

    Lemma th1 : le_decide = le_decide.
      reflexivity.
    Qed.

    Lemma th2 : min = min.
      reflexivity.
    Qed.

  End M.

  (* Checks that Compare and List are loaded *)
  Check Compare.le_decide.
  Check Min.min.


  (* Checks that Compare and List are _not_ imported *)
  Lemma th1 : le_decide = 1.
    reflexivity.
  Qed.

  Lemma th2 : min = 0.
    reflexivity.
  Qed.

  (* It should still be the case after Import M *)
  Import M.

  Lemma th3 : le_decide = 1.
    reflexivity.
  Qed.

  Lemma th4 : min = 0.
    reflexivity.
  Qed.

End Test_Require.

(****************************************************************)

Module Test_Import.
  Module M.
    Import Compare.              (* Imports Min as well *)

    Lemma th1 : le_decide = le_decide.
      reflexivity.
    Qed.

    Lemma th2 : min = min.
      reflexivity.
    Qed.

  End M.

  (* Checks that Compare and List are loaded *)
  Check Compare.le_decide.
  Check Min.min.


  (* Checks that Compare and List are _not_ imported *)
  Lemma th1 : le_decide = 1.
    reflexivity.
  Qed.

  Lemma th2 : min = 0.
    reflexivity.
  Qed.

  (* It should still be the case after Import M *)
  Import M.

  Lemma th3 : le_decide = 1.
    reflexivity.
  Qed.

  Lemma th4 : min = 0.
    reflexivity.
  Qed.
End Test_Import.

(************************************************************************)

Module Test_Export.
  Module M.
    Export Compare.              (* Exports Min as well *)

    Lemma th1 : le_decide = le_decide.
      reflexivity.
    Qed.

    Lemma th2 : min = min.
      reflexivity.
    Qed.

  End M.


  (* Checks that Compare and List are _not_ imported *)
  Lemma th1 : le_decide = 1.
    reflexivity.
  Qed.

  Lemma th2 : min = 0.
    reflexivity.
  Qed.


  (* After Import M they should be imported as well *)

  Import M.

  Lemma th3 : le_decide = le_decide.
    reflexivity.
  Qed.

  Lemma th4 : min = min.
    reflexivity.
  Qed.
End Test_Export.


(************************************************************************)

Module Test_Require_Export.

  Definition mult_sym := 1.    (* from Arith/Mult *)
  Definition plus_sym := 0.        (* from Arith/Plus *)

  Module M.
    Require Export Mult.         (* Exports Plus as well *)

    Lemma th1 : mult_comm = mult_comm.
      reflexivity.
    Qed.

    Lemma th2 : plus_comm = plus_comm.
      reflexivity.
    Qed.

  End M.


  (* Checks that Mult and Plus are _not_ imported *)
  Lemma th1 : mult_sym = 1.
    reflexivity.
  Qed.

  Lemma th2 : plus_sym = 0.
    reflexivity.
  Qed.


  (* After Import M they should be imported as well *)

  Import M.

  Lemma th3 : mult_comm = mult_comm.
    reflexivity.
  Qed.

  Lemma th4 : plus_comm = plus_comm.
    reflexivity.
  Qed.

End Test_Require_Export.
