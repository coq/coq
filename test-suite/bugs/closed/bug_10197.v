(* Some check about implicit arguments in fix *)

Check fix f {f:nat} := match f with 0 => true | _ => false end.

CoInductive stream := { this : nat ; next : option stream }.

Check cofix f {f:nat} := {| this := f ; next := None |}.

(* The following was ok from 8.4, just checking that the order is not
   mixed up accidentally *)

Check fix f (x : nat) (x : forall {a:nat}, a = 0 -> nat) :=
   match x eq_refl with 0 => true | _ => false end.

Check fix f (x : forall {a:nat}, a = 0 -> bool) (x : nat) :=
   match x with 0 => true | _ => false end.
