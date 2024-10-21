From Stdlib Require Import NsatzTactic.
(** Ensure that loading the nsatz tactic doesn't load the reals *)
Fail Module M := Stdlib.Reals.Rdefinitions.
(** Ensure that loading the nsatz tactic doesn't load classic *)
Fail Check Stdlib.Logic.Classical_Prop.classic.
(** Ensure that this test-case hasn't messed up about the location of the reals / how to check for them *)
From Stdlib Require Rdefinitions.
Module M := Stdlib.Reals.Rdefinitions.
(** Ensure that this test-case hasn't messed up about the location of classic / how to check for it *)
From Stdlib Require Classical_Prop.
Check Stdlib.Logic.Classical_Prop.classic.
