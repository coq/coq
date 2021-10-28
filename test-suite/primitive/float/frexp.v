Require Import ZArith Floats.

Definition denorm := Eval compute in Z.ldexp one (-1074)%Z.
Definition neg_one := Eval compute in (-one)%float.

Check (eq_refl : let (m,e) := Z.frexp infinity in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF infinity)).
Check (eq_refl (SFfrexp prec emax (Prim2SF infinity)) <: let (m,e) := Z.frexp infinity in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF infinity)).
Check (eq_refl (SFfrexp prec emax (Prim2SF infinity)) <<: let (m,e) := Z.frexp infinity in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF infinity)).

Check (eq_refl : let (m,e) := Z.frexp nan in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF nan)).
Check (eq_refl (SFfrexp prec emax (Prim2SF nan)) <: let (m,e) := Z.frexp nan in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF nan)).
Check (eq_refl (SFfrexp prec emax (Prim2SF nan)) <<: let (m,e) := Z.frexp nan in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF nan)).

Check (eq_refl : let (m,e) := Z.frexp zero in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF zero)).
Check (eq_refl (SFfrexp prec emax (Prim2SF zero)) <: let (m,e) := Z.frexp zero in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF zero)).
Check (eq_refl (SFfrexp prec emax (Prim2SF zero)) <<: let (m,e) := Z.frexp zero in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF zero)).

Check (eq_refl : let (m,e) := Z.frexp one in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF one)).
Check (eq_refl (SFfrexp prec emax (Prim2SF one)) <: let (m,e) := Z.frexp one in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF one)).
Check (eq_refl (SFfrexp prec emax (Prim2SF one)) <<: let (m,e) := Z.frexp one in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF one)).

Check (eq_refl : let (m,e) := Z.frexp neg_one in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF neg_one)).
Check (eq_refl (SFfrexp prec emax (Prim2SF neg_one)) <: let (m,e) := Z.frexp neg_one in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF neg_one)).
Check (eq_refl (SFfrexp prec emax (Prim2SF neg_one)) <<: let (m,e) := Z.frexp neg_one in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF neg_one)).

Check (eq_refl : let (m,e) := Z.frexp denorm in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF denorm)).
Check (eq_refl (SFfrexp prec emax (Prim2SF denorm)) <: let (m,e) := Z.frexp denorm in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF denorm)).
Check (eq_refl (SFfrexp prec emax (Prim2SF denorm)) <<: let (m,e) := Z.frexp denorm in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF denorm)).
