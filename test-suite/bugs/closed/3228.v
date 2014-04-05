(* Check that variables in the context do not take precedence over
   ltac variables *)

Ltac bar x := exact x.
Goal False -> False.
  intro x.
  Fail bar doesnotexist.
