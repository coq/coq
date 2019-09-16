Require Import Coq.Program.Tactics.

Ltac test n :=
  (*let __ := match goal with _ => idtac n end in*)
  lazymatch n with
  | O => let __ := match goal with _ => assert True by rapply I; clear end in
         uconstr:(fun _ => I)
  | S ?n'
    => let lem := test n' in
       let __ := match goal with _ => assert True by (unshelve rapply lem; try exact I); clear end in
       uconstr:(fun _ : True => lem)
  end.

Goal True.
  assert True by rapply I.
  assert True by (unshelve rapply (fun _ => I); try exact I).
  assert True by (unshelve rapply (fun _ _ => I); try exact I).
  assert True by (unshelve rapply (fun _ _ _ => I); try exact I).
  clear.
  Time let __ := test 50 in idtac.
  rapply I.
Qed.
