Require Import micromega.MExtraction.
Require Import RingMicromega.
Require Import QArith.
Require Import VarMap.
Require Import ZMicromega.
Require Import QMicromega.
Require Import RMicromega.

Recursive Extraction
  List.map RingMicromega.simpl_cone (*map_cone  indexes*)
  denorm Qpower vm_add
  n_of_Z N.of_nat ZTautoChecker ZWeakChecker QTautoChecker RTautoChecker find.
