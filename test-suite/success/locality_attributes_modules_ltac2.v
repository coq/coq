(** This file tests how locality attributes affect usual vernacular commands.
    PLEASE, when this file fails to compute following a voluntary change in
    Coq's behaviour, modify accordingly the tables in [sections.rst] and
    [modules.rst] in [doc/sphinx/language/core] *)

From Ltac2 Require Import Ltac2.

(** ** Tests for modules and visibility attributes with Ltac2 *)

(* A parameter: *)
Parameter (secret : nat).
(* An axiom: *)
Axiom secret_is_42 : secret = 42.

(** *** Without attribute (default) *)

Module InModuleDefault.

Module Bar.
  (* A custom tactic: *)
  Ltac2 find_secret () := rewrite secret_is_42.
  Ltac2 Notation "rfl" := reflexivity.
End Bar.

(** **** Without importing: *)

(* Availability of the tactic *)
Fail Print find_secret.
Print Bar.find_secret.
(* Availability of the tactic notation *)
Lemma plop_ni : 2 + 2 = 4.
Proof. Fail rfl. Admitted.

(** **** After importing: *)

Import Bar.
(* Availability of the tactic *)
Print find_secret.
Print Bar.find_secret.
(* Availability of the tactic notation *)
Lemma plop_i : 2 + 2 = 4.
Proof. rfl. Qed.

End InModuleDefault.

Module InModuleLocal.
Module Bar.
  #[local]
  Ltac2 find_secret () := rewrite secret_is_42.
  #[local]
  Ltac2 Notation "rfl" := reflexivity.
End Bar.

(** **** Without importing: *)

(* Availability of the tactic *)
Fail Print find_secret.
Fail Print Bar.find_secret.
(* Availability of the tactic notation *)
Lemma plop_ni : 2 + 2 = 4.
Proof. Fail rfl. Admitted.

(** **** After importing: *)

Import Bar.
(* Availability of the tactic *)
Fail Print find_secret.
Fail Print Bar.find_secret.
(* Availability of the tactic notation *)
Lemma plop_i : 2 + 2 = 4.
Proof. Fail rfl. Admitted.

End InModuleLocal.

Module InModuleExport.
Module Bar.
  (* A custom tactic: *)
  Fail #[export]
  Ltac2 find_secret := reflexivity.
  (* A tactic notation: *)
  Fail #[export]
  Ltac2 Notation "rfl" := reflexivity.
End Bar.

(** Nothing to check, Ltac2 and Ltac2 Notation do not support the [export]
   attribute. *)

End InModuleExport.

Module InModuleGlobal.
Module Bar.
  #[global]
  Ltac2 find_secret () := rewrite secret_is_42.
  (* A tactic notation: *)
  #[global]
  Ltac2 Notation "rfl" := reflexivity.
End Bar.

(** **** Without importing: *)

(* Availability of the tactic *)
Fail Print find_secret.
Print Bar.find_secret.
(* Availability of the tactic notation *)
Lemma plop_ni : 2 + 2 = 4.
Proof. Fail rfl. Admitted.

(** **** After importing: *)

Import Bar.
Print find_secret.
Print Bar.find_secret.
(* Availability of the tactic notation *)
Lemma plop_i : 2 + 2 = 4.
Proof. rfl. Qed.
End InModuleGlobal.
