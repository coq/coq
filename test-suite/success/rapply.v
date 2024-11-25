Require Import Corelib.Program.Tactics.

(** We make a version of [rapply] that takes [uconstr]; we do not
currently test what scope [rapply] interprets terms in. *)

Tactic Notation "urapply" uconstr(p) := rapply p.

Ltac test n :=
  (*let __ := match goal with _ => idtac n end in*)
  lazymatch n with
  | O => let __ := match goal with _ => assert True by urapply I; clear end in
         uconstr:(fun _ => I)
  | S ?n'
    => let lem := test n' in
       let __ := match goal with _ => assert True by (unshelve urapply lem; try exact I); clear end in
       uconstr:(fun _ : True => lem)
  end.

Goal True.
  assert True by urapply I.
  assert True by (unshelve urapply (fun _ => I); try exact I).
  assert True by (unshelve urapply (fun _ _ => I); try exact I).
  assert True by (unshelve urapply (fun _ _ _ => I); try exact I).
  clear.
  Time let __ := test 50 in idtac.
  urapply I.
Qed.
