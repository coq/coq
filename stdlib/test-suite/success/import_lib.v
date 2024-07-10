Definition le_trans := 0.


Module Test_Read.
  Module M.
From Stdlib Require PeanoNat.        (* Reading without importing *)

    Check PeanoNat.Nat.le_trans.

    Lemma th0 : le_trans = 0.
      reflexivity.
    Qed.
  End M.

  Check PeanoNat.Nat.le_trans.

  Lemma th0 : le_trans = 0.
    reflexivity.
  Qed.

  Import M.

  Lemma th1 : le_trans = 0.
    reflexivity.
  Qed.
End Test_Read.


(****************************************************************)

(* Arith.Compare containes Require Export Wf_nat. *)
Definition le_decide := 1.  (* from Arith/Compare *)
Definition lt_wf := 0.      (* from Arith/Wf_nat *)

Module Test_Require.

  Module M.
From Stdlib Require Import Compare.              (* Imports Compare_dec as well *)

    Lemma th1 n : le_decide n = le_decide n.
      reflexivity.
    Qed.

    Lemma th2 n : lt_wf n = lt_wf n.
      reflexivity.
    Qed.

  End M.

  (* Checks that Compare and Wf_nat are loaded *)
  Check Compare.le_decide.
  Check Wf_nat.lt_wf.


  (* Checks that Compare and Wf_nat are _not_ imported *)
  Lemma th1 : le_decide = 1.
    reflexivity.
  Qed.

  Lemma th2 : lt_wf = 0.
    reflexivity.
  Qed.

  (* It should still be the case after Import M *)
  Import M.

  Lemma th3 : le_decide = 1.
    reflexivity.
  Qed.

  Lemma th4 : lt_wf = 0.
    reflexivity.
  Qed.

End Test_Require.

(****************************************************************)

Module Test_Import.
  Module M.
    Import Compare.              (* Imports Wf_nat as well *)

    Lemma th1 n : le_decide n = le_decide n.
      reflexivity.
    Qed.

    Lemma th2 n : lt_wf n = lt_wf n.
      reflexivity.
    Qed.

  End M.

  (* Checks that Compare and Wf_nat are loaded *)
  Check Compare.le_decide.
  Check Wf_nat.lt_wf.


  (* Checks that Compare and Wf_nat are _not_ imported *)
  Lemma th1 : le_decide = 1.
    reflexivity.
  Qed.

  Lemma th2 : lt_wf = 0.
    reflexivity.
  Qed.

  (* It should still be the case after Import M *)
  Import M.

  Lemma th3 : le_decide = 1.
    reflexivity.
  Qed.

  Lemma th4 : lt_wf = 0.
    reflexivity.
  Qed.
End Test_Import.

(************************************************************************)

Module Test_Export.
  Module M.
    Export Compare.              (* Exports Wf_nat as well *)

    Lemma th1 n : le_decide n = le_decide n.
      reflexivity.
    Qed.

    Lemma th2 n : lt_wf n = lt_wf n.
      reflexivity.
    Qed.

  End M.


  (* Checks that Compare and Wf_nat are _not_ imported *)
  Lemma th1 : le_decide = 1.
    reflexivity.
  Qed.

  Lemma th2 : lt_wf = 0.
    reflexivity.
  Qed.


  (* After Import M they should be imported as well *)

  Import M.

  Lemma th3 n : le_decide n = le_decide n.
    reflexivity.
  Qed.

  Lemma th4 n : lt_wf n = lt_wf n.
    reflexivity.
  Qed.
End Test_Export.


(************************************************************************)

Module Test_Require_Export.

  Definition le_decide := 1.    (* from Arith/Compare *)
  Definition lt_wf := 0.        (* from Arith/Wf_nat *)

  Module M.
From Stdlib Require Export Compare.       (* Exports Wf_nat as well *)

    Lemma th1 n : le_decide n = le_decide n.
      reflexivity.
    Qed.

    Lemma th2 n : lt_wf n = lt_wf n.
      reflexivity.
    Qed.

  End M.


  (* Checks that Compare and Wf_nat are _not_ imported *)
  Lemma th1 : le_decide = 1.
    reflexivity.
  Qed.

  Lemma th2 : lt_wf = 0.
    reflexivity.
  Qed.


  (* After Import M they should be imported as well *)

  Import M.

  Lemma th3 n : le_decide n = le_decide n.
    reflexivity.
  Qed.

  Lemma th4 n : lt_wf n = lt_wf n.
    reflexivity.
  Qed.

End Test_Require_Export.
