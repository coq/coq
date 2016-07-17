(* Check a case where ltac typing error should result in error, not anomaly *)

Goal forall (H : forall x : nat, x = x), False.
intro.
Fail
  let H :=
    match goal with
    | [ H : context G [@eq _ _] |- _ ] => let H' := context G[@plus 2] in H'
    end
  in pose H.
