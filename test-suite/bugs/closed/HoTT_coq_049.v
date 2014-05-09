Require Import FunctionalExtensionality.

Goal forall y, @f_equal = y.
intro.
apply functional_extensionality_dep.
(* Error: Ill-typed evar instance in HoTT/coq, Anomaly: Uncaught exception Reductionops.NotASort(_). Please report. before that. *)
