Require Import Ltac2.Ltac2.
Import Constr.Unsafe.
Goal True.
  let e := '_ in
  let ev := match kind e with
            | Evar e _ => e
            | _ => Control.throw (Tactic_failure None)
            end in
  let t := Constr.type e in
  unify $t bool;
  Control.new_goal ev > [ exact I | exact true ].
Qed.
