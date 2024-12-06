From Corelib Require Import ssreflect.
Definition f (x : unit) := True.
Goal exists (x : unit), forall (y : True = f x), True.
eexists ?[x]. intros.
Succeed rewrite y.
Succeed rewrite (y : _).
Succeed rewrite (y : True = _).
Succeed rewrite (y : True = f ?x).
Fail rewrite (y : True = f _).
Fail rewrite (_ : True = f _).
Abort.
