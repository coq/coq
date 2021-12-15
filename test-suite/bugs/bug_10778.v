(* Test that fresh avoid the variables of intro patterns but also of
   simple intro patterns *)

Ltac exploit_main t T pat cleanup
  :=
  (lazymatch T with
   | ?U1 -> ?U2 =>
       let H := fresh
       in
idtac "H=" H;
         assert U1 as H;
         [cleanup () | exploit_main (t H) U2 pat ltac:(fun _ => clear H; cleanup ())]
   | _ =>
       pose proof t as pat;
       cleanup ()
   end).

Tactic Notation "exploit" constr(t) "as" simple_intropattern(pat)
  :=
  exploit_main t ltac:(type of t) pat ltac:(fun _ => idtac).

Goal (True -> True) -> True.
intro H0. exploit H0 as H.
Abort.

Tactic Notation "exploit'" constr(t) "as" intropattern(pat)
  :=
  exploit_main t ltac:(type of t) pat ltac:(fun _ => idtac).

Goal (True -> True) -> True.
intro H0. exploit' H0 as H.
Abort.
