Notation "'xbar'" := _.
Fail Check match _ with xbar bli => _ end.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).

Check fun x =>
  match x with
  | <{ pair }> when true => _
  | _ => 1
  end.
