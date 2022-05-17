Require Import Ltac2.Init.
Require Ltac2.Control.
Require Ltac2.Ltac1.

Ltac2 drop_first_success (tac : unit -> 'a) :=
  match Control.case tac with
  | Val v
    => let (first_success, next) := v in
       fun (v : unit) => next (Tactic_failure None)
  | Err err => Control.zero err
  end.

Ltac drop_first_success tac :=
  let f := ltac2:(tac1 |- drop_first_success (fun () => Ltac1.run tac1) ()) in
  f tac.

Ltac drop_n_success n tac :=
  lazymatch n with
  | O => tac
  | S ?n => drop_n_success n ltac:(drop_first_success tac)
  end.

Ltac only_nth_success n tac :=
  once (drop_n_success n tac).

Set Default Proof Mode "Classic".

Goal True \/ False.
  drop_first_success ltac:(idtac "a"; constructor).
(* Error: Uncaught Ltac2 exception: Tactic_failure (None) *)
Abort.
