(* Test parsing/interpretation/pretyping on a large example *)
(* Expected time < 0.10s *)

(* Complexity of unification used to be exponential in the number of nested
   constants, as pointed out by Georges Gonthier and Nicolas Tabareau (a.o.)

   The problem is that unification of id^n+1(0) and id^n+1(1) proceeds as:
   - try not unfold the outermost id by trying to unify its arguments:
     1st rec. call on id^n(0) id^n(1), which fails
   - Coq then tries to unfold id^n+1(k) which produces id^n(k)
   - 2nd rec. call on id^n(0) id^n(1), which also fails
   Complexity is thus at least exponential.

   This is fixed (in the ground case), by the fact that when we try to
   unify two ground terms (ie. without unsolved evars), we call kernel
   conversion and if this fails, then the terms are not unifiable.
   Hopefully, kernel conversion is not exponential on cases like the one
   below thanks to sharing (as long as unfolding the fonction does not
   use its argument under a binder).

   There are probably still many cases where unification goes astray.
 *)


Definition id (n:nat) := n.
Goal
  (id (id (id (id
  (id (id (id (id
  (id (id (id (id
  (id (id (id (id
  (id (id (id (id
   0
   ))))
   ))))
   ))))
   ))))
   ))))
   =
  (id (id (id (id
  (id (id (id (id
  (id (id (id (id
  (id (id (id (id
  (id (id (id (id
   1
   ))))
   ))))
   ))))
   ))))
   ))))
.
Timeout 2 Time try refine (refl_equal _).
