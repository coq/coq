(** This file tests how locality attributes affect usual vernacular commands.
    PLEASE, when this file fails to compute following a voluntary change in
    Coq's behaviour, modify accordingly the tables in [sections.rst] and
    [modules.rst] in [doc/sphinx/language/core] *)

From Ltac2 Require Import Ltac2.

(** ** Tests for sections and visibility attributes with Ltac2 *)

(* A parameter: *)
Parameter (secret : nat).
(* An axiom: *)
Axiom secret_is_42 : secret = 42.

(** *** Without attribute (default) *)

Module InSectionDefault.

Section Bar.
  (* A custom tactic: *)
  Ltac2 find_secret () := rewrite secret_is_42.
  Ltac2 Notation "rfl" := reflexivity.
End Bar.

(* Availability of the tactic *)
Fail Print find_secret.
(* Availability of the tactic notation *)
Lemma plop_ni : 2 + 2 = 4.
Proof. Fail rfl. Admitted.

End InSectionDefault.

Module InSectionLocal.
Section Bar.
  #[local]
  Ltac2 find_secret () := rewrite secret_is_42.
  #[local]
  Ltac2 Notation "rfl" := reflexivity.
End Bar.

(* Availability of the tactic *)
Fail Print find_secret.
Fail Print Bar.find_secret.
(* Availability of the tactic notation *)
Lemma plop_ni : 2 + 2 = 4.
Proof. Fail rfl. Admitted.
End InSectionLocal.

Module InSectionExport.
Section Bar.
  (* A custom tactic: *)
  Fail #[export]
  Ltac2 find_secret := reflexivity.
  (* A tactic notation: *)
  Fail #[export]
  Ltac2 Notation "rfl" := reflexivity.
End Bar.

(** Nothing to check, Ltac2 and Ltac2 Notation do not support the [export]
   attribute. *)

End InSectionExport.

Module InSectionGlobal.
Section Bar.
  (* A custom tactic: *)
  #[global]
  Ltac2 find_secret () := rewrite secret_is_42.
  (* A tactic notation: *)
  #[global]
  Ltac2 Notation "rfl" := reflexivity.
End Bar.

(* Availability of the tactic *)
Fail Print find_secret.
(* Availability of the tactic notation *)
Lemma plop_ni : 2 + 2 = 4.
Proof. Fail rfl. Admitted.
