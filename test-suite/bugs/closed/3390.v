Tactic Notation "basicapply" open_constr(R) "using" tactic3(tac) "sideconditions" tactic0(tacfin) := idtac.
Tactic Notation "basicapply" open_constr(R) := basicapply R using (fun Hlem => idtac) sideconditions (autounfold with spred; idtac).
(* segfault in coqtop *)


Tactic Notation "basicapply" tactic0(tacfin) := idtac.

Goal True.
basicapply subst.
