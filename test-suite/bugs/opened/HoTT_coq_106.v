(* File reduced by coq-bug-finder from 520 lines to 9 lines. *)
Set Universe Polymorphism.
Class IsPointed (A : Type) := point : A.

Generalizable Variables A B f.

Instance ispointed_forall `{H : forall a : A, IsPointed (B a)}
: IsPointed (forall a, B a)
  := fun a => @point (B a) (H a).

Instance ispointed_sigma `{IsPointed A} `{IsPointed (B (point A))}
: IsPointed (sigT B).
(* Message was at some time:
Toplevel input, characters 20-108:
Error: Unable to satisfy the following constraints:
UNDEFINED EVARS:
 ?8==[A H B |- IsPointed (forall x : Type, ?13)] (parameter IsPointed of
       @point)
 ?12==[A H {B} x |- Type] (parameter A of @point)
 ?13==[A H {B} x |- Type] (parameter A of @point)
 ?15==[A H {B} x |- Type] (parameter A of @point)UNIVERSES:
 {Top.38 Top.30 Top.39 Top.40 Top.29 Top.36 Top.31 Top.35 Top.37 Top.34 Top.32 Top.33} |= Top.30 < Top.29
                                                  Top.30 < Top.36
                                                  Top.32 < Top.34
                                                  Top.38 <= Top.37
                                                  Top.38 <= Top.33
                                                  Top.40 <= Top.38
                                                  Top.40 <= Coq.Init.Specif.7
                                                  Top.40 <= Top.39
                                                  Top.36 <= Top.35
                                                  Top.37 <= Top.35
                                                  Top.34 <= Top.31
                                                  Top.32 <= Top.39
                                                  Top.32 <= Coq.Init.Specif.8
                                                  Top.33 <= Top.31

ALGEBRAIC UNIVERSES:
 {Top.38 Top.40 Top.29 Top.36 Top.31 Top.37 Top.34 Top.33}
UNDEFINED UNIVERSES:
 Top.38
 Top.30
 Top.39
 Top.40
 Top.29
 Top.36
 Top.31
 Top.35
 Top.37
 Top.34
 Top.32
 Top.33CONSTRAINTS:[] [A H B] |- ?13 == ?12
[] [A H B H0] |- ?12 == ?15 *)
