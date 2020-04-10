Require Import Coq.nsatz.NsatzTactic.
(** Ensure that loading the nsatz tactic doesn't load the reals *)
Fail Module M := Coq.Reals.Rdefinitions.
(** Ensure that loading the nsatz tactic doesn't load classic *)
Fail Check Coq.Logic.Classical_Prop.classic.
(** Ensure that this test-case hasn't messed up about the location of the reals / how to check for them *)
Require Coq.Reals.Rdefinitions.
Module M := Coq.Reals.Rdefinitions.
(** Ensure that this test-case hasn't messed up about the location of classic / how to check for it *)
Require Coq.Logic.Classical_Prop.
Check Coq.Logic.Classical_Prop.classic.
