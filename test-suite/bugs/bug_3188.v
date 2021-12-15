(* File reduced by coq-bug-finder from 1656 lines to 221 lines to 26 lines to 7 lines. *)

Module Long.
  Require Import Coq.Classes.RelationClasses.

  Hint Extern 0 => apply reflexivity : typeclass_instances.
  Hint Extern 1 => symmetry.

  Lemma foo : exists m' : Type, True.
    intuition. (* Anomaly: Uncaught exception Not_found. Please report. *)
  Abort.
End Long.

Module Short.
  Require Import Coq.Classes.RelationClasses.

  Hint Extern 0 => apply reflexivity : typeclass_instances.

  Lemma foo : exists m' : Type, True.
    try symmetry. (* Anomaly: Uncaught exception Not_found. Please report. *)
  Abort.
End Short.
