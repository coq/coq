Require Corelib.Program.Tactics.

Program Definition foo : True -> False := fun _ => _.

Section bar.
  Context (f : False).

  Fail Next Obligation.
End bar.

Next Obligation. Admitted.
Print foo.
(* foo = fun (f : False) (H : True) => (fun _ : True => foo_obligation_1 f) H
     : False -> True -> False
 *)
