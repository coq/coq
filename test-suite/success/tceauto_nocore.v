(* tc eauto doesn't automatically include core *)
Goal True.
Fail typeclasses eauto.
Succeed typeclasses eauto with core.
Abort.
