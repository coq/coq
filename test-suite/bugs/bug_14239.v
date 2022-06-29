Require Import Setoid Morphisms.

Parameter reli : forall (dummy:unit)(R:relation unit), relation unit.

Parameter f g : unit -> unit.

#[export] Declare Instance c
  (dummy : unit) (R : relation unit) :
  Proper (reli dummy R ==> R) f.

Parameter H : forall (eq : relation unit) (a : unit), eq a a -> eq (g a) a.

Goal f (g tt) = tt.
try rewrite H.
Abort.

Goal f (g tt) = tt.
try setoid_rewrite H.
Abort.
