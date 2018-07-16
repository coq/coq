Require Import ZArith Floats.

Definition denorm := Eval compute in ldexp one (-1074)%Z.
Definition neg_one := Eval compute in (-one)%float.

Check (eq_refl : let (m,e) := frexp infinity in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF infinity)).

Check (eq_refl : let (m,e) := frexp nan in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF nan)).

Check (eq_refl : let (m,e) := frexp zero in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF zero)).

Check (eq_refl : let (m,e) := frexp one in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF one)).

Check (eq_refl : let (m,e) := frexp neg_one in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF neg_one)).

Check (eq_refl : let (m,e) := frexp denorm in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF denorm)).
