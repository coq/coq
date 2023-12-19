Require Import Ltac2.Ltac2.
Require Import Ltac2.Failf.

Ltac2 pose_andb x :=
  let t := Constr.type constr:($x) in
  let r := lazy_match! t with
           | nat => gfail "expected bool, got %t" t
           | bool => constr:(andb $x $x)
           end in
  pose $r.

Goal forall (x: nat) (b: bool), True.
  intros.
  Fail (let r := (if true then gfail "nope" else constr:(1)) in pose $r).
  Fail gfail "The problem is %t" constr:(x + x).
  if false then fail else ().
  if false then fail "nope" else ().
  Fail if true then fail "nope" else ().
  pose_andb 'b.
  Fail pose_andb 'x.
  Fail try (anomaly "testing anomaly notation for nat %t and bool %t" 'x 'b).
  Fail anomaly.
Abort.
