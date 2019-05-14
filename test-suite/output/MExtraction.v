Require Import micromega.MExtraction.
Require Import RingMicromega.
Require Import QArith.
Require Import VarMap.
Require Import ZMicromega.
Require Import QMicromega.
Require Import RMicromega.

Recursive Extraction
Tauto.mapX Tauto.foldA Tauto.collect_annot Tauto.ids_of_formula Tauto.map_bformula
           ZMicromega.cnfZ ZMicromega.Zeval_const ZMicromega.bound_problem_fr QMicromega.cnfQ
           List.map simpl_cone (*map_cone  indexes*)
           denorm Qpower vm_add
   normZ normQ normQ n_of_Z N.of_nat ZTautoChecker ZWeakChecker QTautoChecker RTautoChecker find.
